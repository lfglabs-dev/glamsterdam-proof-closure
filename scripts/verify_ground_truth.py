#!/usr/bin/env python3
r"""
Mechanical Ground-Truth Verifier (`verify_ground_truth.py`) for `glamsterdam-proof-closure`.

Performs 6 structural & mechanical verification passes:
1. Canonical 23-file SHA-256 manifest verification (`vendor/upstreams/SHA256SUMS`):
   - Validates line format (`<64-hex> <rel_path>`), rejects absolute paths, `..` traversal,
     symlinks, non-regular files, and paths resolving outside `vendor/upstreams/`.
   - Enforces canonical-path uniqueness, exact cardinality (23 unique canonical files),
     zero unlisted files in `vendor/upstreams/`, and exact SHA-256 match.
2. Remediation Ledger validation (`audit/remediation-ledger.yaml`):
   - Validates schema, step assignments, canonical vendored upstream files and line ranges,
     and enforces `required_symbols` / `forbidden_symbols` when `--enforce-ledger-step <step>`
     (or full-repo post-remediation check) is active.
3. Two-tier `audit/source-map.yaml` verification:
   - Global structural pass (runs unconditionally on ALL entries even when `--scope` is specified):
     validates YAML syntax, mapping schema, `lean_symbol`/`upstream`/`path`/`lines` fields,
     rejects path traversal and symlinked file/directory components via `resolve_safe_vendor_file`,
     and verifies that `lines` are in-bounds for the vendored upstream file.
   - Scoped semantic pass (runs on all entries matching `--scope`, or 100% of entries when unscoped):
     enforces `upstream_symbol` and `mapping_kind` (`exact` or `projection`), verifies the Lean
     declaration exists in the target `.lean` file, and verifies `upstream_symbol` appears with
     identifier boundaries (`\b...\b`) inside the cited upstream line range.
4. Inline docstring citation verification across `Glamsterdam/**/*.lean` and `audit/**/*.md`:
   - Deterministic vendored file index with explicit collision detection (ambiguous suffixes
     matching >1 vendored file are rejected unless disambiguated by path prefix).
   - Every citation matching `([a-zA-Z0-9_./-]+\.(?:py|md)):(\d+)(?:-(\d+))?` must resolve to an
     unambiguous vendored upstream file and in-bounds line numbers.
   - For every `/-- ` docstring header in `Glamsterdam/**/*.lean` that cites both a backticked
     identifier `` `foo` `` and `(file.py:start-end)`, the upstream identifier must appear with
     identifier boundaries within the cited line window.
5. Banned hallucination check across `.lean`, `.yaml` (except `remediation-ledger.yaml`), `.md`,
   and `tests/**/*.py` files.
6. Scoped verification (`--scope <subpath>`): allows verifying zero errors on remediated modules
   in Steps 2, 3, 4, 5, and full repository zero-error verification in Step 6.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import sys
import tempfile
import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent.resolve()
VENDOR_DIR = (ROOT / "vendor" / "upstreams").resolve()
EXPECTED_VENDOR_FILE_COUNT = 23
HEX64_RE = re.compile(r"^[0-9a-f]{64}$")
LEAN_SYMBOL_RE = re.compile(r"^Glamsterdam(?:\.[A-Za-z0-9_]+){2,}$")
EXPECTED_LEDGER_IDS = [
    "M1-STATE-TRACKER-MODIFY-STATE",
    "M2-SYS-TX-RESERVOIR-SEMANTICS",
    "M3-DELEGATION-CREATE-EVM-ORDERING",
    "M4-GLOAS-FIRST-PRINCIPLES-AND-SLASH-VALIDATOR",
    "M5-READ-TRACKING-PROJECTION-BOUNDARY",
    "M6-EIP8246-BAL-FULL-SLICE",
]

BANNED_PATTERNS = [
    (r"PR\s*#5170\b", "Hallucinated PR #5170 (actually a mypy dependency bump)"),
    (r"PR\s*#5172\b", "Hallucinated PR #5172 (actually 'Fix genesis state in Gloas'; target equivocation is PR #5543)"),
    (r"\bwill_participate\b", "Hallucinated identifier `will_participate` (actual variables are `had_no_participation` and `will_set_new_flag`)"),
    (r"\bSYS_TX_GAS_LIMIT\b", "Hallucinated identifier `SYS_TX_GAS_LIMIT` (actual constant in `fork.py:107` is `SYSTEM_TRANSACTION_GAS`)"),
    (r"\bonboarded_builders\b", "Hallucinated identifier `onboarded_builders` (not in `v1.7.0-beta.4` `fork.md`)"),
    (r"\bel_vm_gas\.py\b", "Hallucinated filename `el_vm_gas.py` (actual path is `vm/gas.py`)"),
    (r"\bel_fork\.py\b", "Hallucinated filename `el_fork.py` (actual path is `fork.py`)"),
    (r"F-7732-EARLIER-SLOT-PROPOSER-SLASHING-NOT-CLEARED", "Hallucinated Finding 1.5 based on misquoted `slash_validator`"),
    (r"slash_pending_payment_v170_beta4_buggy", "Hallucinated buggy `slash_validator` helper (v1.7.0-beta.4 loops over all `builder_pending_payments`)"),
    (r"slashed_index\s*==\s*state\.latest_block_header\.proposer_index", "Misquoted `slash_validator` condition (v1.7.0-beta.4 checks `payment.proposer_index == slashed_index`)"),
    (r"set_delegation\(message\)", "Misquoted `set_delegation(message)` call (actual call in `create_evm` at `interpreter.py:161` is `set_delegation(block_env, tx_env, gas_meter)`)"),
    (r"set_account_balance_zero_creates_empty_leaf", "Hallucinated theorem based on misreading `set_account_balance` (`state_tracker.py:663-684` DOES call `modify_state`)"),
    (r"set_account_balance\s+calls\s+`?set_account`?\s+directly\s+WITHOUT\s+`?modify_state`?", "Hallucinated claim about `set_account_balance` (`state_tracker.py:683` calls `modify_state`)"),
    (r"sys_tx_initial_meter_v16898000", "Hallucinated system-tx gas meter mutant claiming `state_gas_left = 0` (`fork.py:759-761` sets `state_gas_reservoir = STORAGE_SET * SYSTEM_MAX_SSTORES_PER_CALL`)"),
    (r"F-8037-SYS-TX-GAS-LIMIT-INVARIANT", "Hallucinated Finding 2.5 claiming `state_gas_left = 0` in `process_unchecked_system_transaction`"),
    (r"`?else`?\s+branch\s+at\s+line\s+94\b", "Misquoted line number in `fork.md` (`else:` branch in `onboard_builders_from_pending_deposits` is at lines 115-117, not 94)"),
    (r"\bprocess_proposer_slashing\b", "Hallucinated/wrong function name `process_proposer_slashing` for builder payment clearing (actual function in `beacon-chain.md:1549-1582` is `slash_validator`)"),
    (r"\bon_payload_attestation\b", "Out-of-scope or hallucinated function `on_payload_attestation` (in-scope attestation function in `beacon-chain.md:2396-2481` is `process_attestation`)"),
    (r"\b10_000\b", "Banned underscore literal `10_000`"),
    (r"\b1115-1143\b", "Hallucinated line range `1115-1143` for `allocate_evm_gas` (actual range in `vm/gas.py` is `1105-1138`)"),
]


def has_symlink_component(base_dir: pathlib.Path, raw_path: pathlib.PurePosixPath) -> str | None:
    cur = base_dir
    for part in raw_path.parts:
        cur = cur / part
        if cur.is_symlink():
            return part
    return None


def resolve_safe_vendor_file(rel_str: str) -> tuple[pathlib.Path | None, str | None, str | None]:
    raw_path = pathlib.PurePosixPath(str(rel_str))
    if not str(rel_str) or raw_path.is_absolute() or ".." in raw_path.parts:
        return None, None, f"Unsafe relative path `{rel_str}` (empty, absolute, or contains `..`)"
    sym_part = has_symlink_component(VENDOR_DIR, raw_path)
    if sym_part is not None:
        return None, None, f"Symlink component `{sym_part}` not allowed in vendor/upstreams path: `{rel_str}`"
    candidate = VENDOR_DIR / str(rel_str)
    resolved = candidate.resolve()
    try:
        canon_rel = resolved.relative_to(VENDOR_DIR).as_posix()
    except ValueError:
        return None, None, f"Path escapes vendor/upstreams: `{rel_str}`"
    if not resolved.exists() or not resolved.is_file():
        return None, None, f"Missing or non-regular vendored file: `{rel_str}`"
    return resolved, canon_rel, None


def index_vendored_rel_paths(rel_map: dict[str, pathlib.Path]) -> tuple[dict[str, pathlib.Path], set[str]]:
    idx: dict[str, pathlib.Path] = {}
    ambiguous: set[str] = set()

    def register(key: str, target: pathlib.Path) -> None:
        if key in ambiguous:
            return
        if key in idx and idx[key] != target:
            ambiguous.add(key)
            idx.pop(key, None)
        else:
            idx[key] = target

    for rel in sorted(rel_map.keys()):
        p = rel_map[rel]
        register(rel, p)
        parts = rel.split("/")
        for i in range(1, len(parts)):
            suffix = "/".join(parts[i:])
            register(suffix, p)
    return idx, ambiguous


def build_vendored_file_index() -> tuple[dict[str, pathlib.Path], set[str]]:
    rel_map: dict[str, pathlib.Path] = {}
    for raw_p in sorted(VENDOR_DIR.rglob("*")):
        if raw_p.name == "SHA256SUMS" or raw_p.is_symlink() or not raw_p.is_file():
            continue
        try:
            rel_cand = raw_p.relative_to(VENDOR_DIR).as_posix()
        except ValueError:
            continue
        resolved, canon_rel, err = resolve_safe_vendor_file(rel_cand)
        if err is None and resolved is not None and canon_rel is not None:
            rel_map[canon_rel] = resolved
    return index_vendored_rel_paths(rel_map)


def check_sha256sums() -> tuple[list[str], int]:
    errors = []
    sums_file = VENDOR_DIR / "SHA256SUMS"
    if not sums_file.exists() or sums_file.is_symlink() or not sums_file.is_file():
        return [f"[sha256sums] Missing or invalid {sums_file}"], 0
    seen_canonical: set[str] = set()
    lines = [ln.strip() for ln in sums_file.read_text().splitlines() if ln.strip()]
    if len(lines) != EXPECTED_VENDOR_FILE_COUNT:
        errors.append(
            f"[sha256sums] Expected exactly {EXPECTED_VENDOR_FILE_COUNT} entries in SHA256SUMS, found {len(lines)}"
        )
    for line_no, line in enumerate(lines, 1):
        parts = line.split(None, 1)
        if len(parts) != 2:
            errors.append(f"[sha256sums] Malformed line {line_no} in SHA256SUMS: `{line}`")
            continue
        expected_hash, rel_path = parts[0].strip(), parts[1].strip()
        if not HEX64_RE.match(expected_hash):
            errors.append(f"[sha256sums] Invalid SHA-256 hex digest on line {line_no}: `{expected_hash}`")
            continue
        f_path, canon_rel, err = resolve_safe_vendor_file(rel_path)
        if err or f_path is None or canon_rel is None:
            errors.append(f"[sha256sums] Line {line_no}: {err}")
            continue
        if canon_rel != rel_path:
            errors.append(f"[sha256sums] Non-canonical path `{rel_path}` (canonical is `{canon_rel}`)")
        if canon_rel in seen_canonical:
            errors.append(f"[sha256sums] Duplicate canonical entry in SHA256SUMS: `{canon_rel}`")
        seen_canonical.add(canon_rel)
        actual_hash = hashlib.sha256(f_path.read_bytes()).hexdigest()
        if actual_hash != expected_hash:
            errors.append(f"[sha256sums] SHA-256 mismatch for {canon_rel}: expected {expected_hash}, got {actual_hash}")

    actual_files: set[str] = set()
    for p in VENDOR_DIR.rglob("*"):
        if p.name == "SHA256SUMS":
            continue
        if p.is_symlink():
            errors.append(f"[sha256sums] Forbidden symlink in vendor/upstreams: {p}")
        elif p.is_file():
            try:
                rel_cand = p.relative_to(VENDOR_DIR).as_posix()
            except ValueError:
                errors.append(f"[sha256sums] Path outside vendor/upstreams: {p}")
                continue
            _, canon_rel, err = resolve_safe_vendor_file(rel_cand)
            if err or canon_rel is None:
                errors.append(f"[sha256sums] Unsafe file in vendor/upstreams: {err}")
            else:
                actual_files.add(canon_rel)
        elif not p.is_dir():
            errors.append(f"[sha256sums] Forbidden non-regular entry (FIFO/socket/device) in vendor/upstreams: {p}")

    unlisted = sorted(actual_files - seen_canonical)
    for u in unlisted:
        errors.append(f"[sha256sums] Unlisted file in vendor/upstreams not in SHA256SUMS: {u}")
    if len(seen_canonical) != EXPECTED_VENDOR_FILE_COUNT:
        errors.append(
            f"[sha256sums] Unique canonical file count is {len(seen_canonical)}, expected {EXPECTED_VENDOR_FILE_COUNT}"
        )
    return errors, len(seen_canonical)


def resolve_safe_repo_file(rel_str: str) -> tuple[pathlib.Path | None, str | None, str | None]:
    raw_path = pathlib.PurePosixPath(str(rel_str))
    if not str(rel_str) or raw_path.is_absolute() or ".." in raw_path.parts:
        return None, None, f"Unsafe relative repo path `{rel_str}` (empty, absolute, or contains `..`)"
    sym_part = has_symlink_component(ROOT, raw_path)
    if sym_part is not None:
        return None, None, f"Symlink component `{sym_part}` not allowed for target repo file: `{rel_str}`"
    candidate = ROOT / str(rel_str)
    resolved = candidate.resolve()
    try:
        canon_rel = resolved.relative_to(ROOT).as_posix()
    except ValueError:
        return None, None, f"Path escapes repository root: `{rel_str}`"
    if not resolved.exists() or not resolved.is_file():
        return None, None, f"Missing or non-regular repository file: `{rel_str}`"
    return resolved, canon_rel, None


def parse_line_ranges(spec: str) -> tuple[list[tuple[int, int]], str | None]:
    ranges = []
    if spec is None or str(spec).strip() == "":
        return [], "Empty line range specification"
    for part in str(spec).split(","):
        part = part.strip()
        try:
            if "-" in part:
                s, e = part.split("-", 1)
                ranges.append((int(s), int(e)))
            else:
                n = int(part)
                ranges.append((n, n))
        except ValueError:
            return [], f"Malformed line range `{part}` in `{spec}`"
    return ranges, None


def safe_load_yaml_text(raw_text: str, label: str) -> tuple[object, str | None]:
    try:
        return yaml.safe_load(raw_text), None
    except yaml.YAMLError as exc:
        return None, f"[{label}] Malformed YAML: {exc}"


def validate_ledger_data(data: object, enforce_steps: list[str] | None = None) -> tuple[list[str], int]:
    errors = []
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        return ["[remediation-ledger] Invalid top-level YAML structure or schema_version != 1"], 0
    if not isinstance(data.get("description"), str) or not data["description"].strip():
        errors.append("[remediation-ledger] Missing or non-string top-level `description`")
    items = data.get("items")
    if not isinstance(items, list) or len(items) != len(EXPECTED_LEDGER_IDS):
        errors.append(
            f"[remediation-ledger] Expected a list of exactly {len(EXPECTED_LEDGER_IDS)} ledger items ({EXPECTED_LEDGER_IDS}), found {len(items) if isinstance(items, list) else type(items).__name__}"
        )
        if not isinstance(items, list):
            return errors, 0

    seen_ids: list[str] = []
    valid_steps = {"step2", "step3", "step4", "step5", "step6"}
    for idx, item in enumerate(items):
        if not isinstance(item, dict):
            errors.append(f"[remediation-ledger] Item #{idx} is not a mapping")
            continue
        item_id = item.get("id")
        if not isinstance(item_id, str) or not item_id.strip():
            errors.append(f"[remediation-ledger] Item #{idx} has missing/invalid `id`")
            continue
        if item_id in seen_ids:
            errors.append(f"[remediation-ledger] Duplicate item id `{item_id}`")
        seen_ids.append(item_id)

        step = item.get("step")
        if not isinstance(step, str) or step not in valid_steps:
            errors.append(f"[remediation-ledger] {item_id}: invalid `step` `{step}` (expected one of {sorted(valid_steps)})")

        for req_str_field in ("target_file", "upstream_file", "upstream_lines", "description"):
            val = item.get(req_str_field)
            if not isinstance(val, str) or not val.strip():
                errors.append(f"[remediation-ledger] {item_id}: `{req_str_field}` must be a non-empty string")

        target_rel = item.get("target_file")
        up_rel = item.get("upstream_file")
        up_lines_spec = item.get("upstream_lines")
        req_syms = item.get("required_symbols")
        forb_syms = item.get("forbidden_symbols")

        if not isinstance(req_syms, list) or len(req_syms) == 0 or not all(isinstance(s, str) and s.strip() for s in req_syms):
            errors.append(f"[remediation-ledger] {item_id}: `required_symbols` must be a non-empty list of non-empty strings")
            req_syms = []
        if not isinstance(forb_syms, list) or not all(isinstance(s, str) and s.strip() for s in forb_syms):
            errors.append(f"[remediation-ledger] {item_id}: `forbidden_symbols` must be a list of non-empty strings")
            forb_syms = []

        if not isinstance(target_rel, str) or not isinstance(up_rel, str) or not isinstance(up_lines_spec, str):
            continue

        target_path, target_canon, t_err = resolve_safe_repo_file(target_rel)
        if t_err or target_path is None:
            errors.append(f"[remediation-ledger] {item_id}: invalid target_file `{target_rel}` ({t_err})")
            continue
        if target_canon != target_rel:
            errors.append(f"[remediation-ledger] {item_id}: non-canonical target_file `{target_rel}`")

        up_path, _, err = resolve_safe_vendor_file(up_rel)
        if err or up_path is None:
            errors.append(f"[remediation-ledger] {item_id}: invalid upstream_file `{up_rel}` ({err})")
            continue
        up_lines = up_path.read_text().splitlines()
        ranges, r_err = parse_line_ranges(up_lines_spec)
        if r_err:
            errors.append(f"[remediation-ledger] {item_id}: {r_err}")
            continue
        for s, e in ranges:
            if s < 1 or e > len(up_lines) or s > e:
                errors.append(
                    f"[remediation-ledger] {item_id}: out-of-bounds upstream_lines {s}-{e} in {up_rel} ({len(up_lines)} lines)"
                )

        if enforce_steps and (step in enforce_steps or "all" in enforce_steps):
            target_text = target_path.read_text()
            for req_sym in req_syms:
                if not re.search(rf"\b{re.escape(req_sym)}\b", target_text):
                    errors.append(
                        f"[remediation-ledger] {item_id} ({step}): required symbol `{req_sym}` missing in {target_rel}"
                    )
            for forb_sym in forb_syms:
                if re.search(rf"\b{re.escape(forb_sym)}\b", target_text):
                    errors.append(
                        f"[remediation-ledger] {item_id} ({step}): forbidden symbol `{forb_sym}` still present in {target_rel}"
                    )

    if seen_ids != EXPECTED_LEDGER_IDS:
        errors.append(
            f"[remediation-ledger] Ledger item IDs {seen_ids} do not match required ordered set {EXPECTED_LEDGER_IDS}"
        )
    return errors, len(items)


def check_remediation_ledger(enforce_steps: list[str] | None = None) -> tuple[list[str], int]:
    ledger_path = ROOT / "audit" / "remediation-ledger.yaml"
    if not ledger_path.exists() or ledger_path.is_symlink() or not ledger_path.is_file():
        return ["[remediation-ledger] Missing or invalid audit/remediation-ledger.yaml"], 0
    data, y_err = safe_load_yaml_text(ledger_path.read_text(), "remediation-ledger")
    if y_err:
        return [y_err], 0
    return validate_ledger_data(data, enforce_steps)


def lean_module_to_path(lean_symbol: str) -> tuple[pathlib.Path | None, str | None, str | None, str | None]:
    if not isinstance(lean_symbol, str) or not LEAN_SYMBOL_RE.match(lean_symbol):
        return (
            None,
            None,
            None,
            f"Invalid `lean_symbol` format `{lean_symbol}` (must match `Glamsterdam.<Module>.<symbol>`)",
        )
    parts = lean_symbol.split(".")
    # Enforce single-token declaration suffix: module path is strictly `parts[:-1]`, declaration is `parts[-1]`.
    if len(parts) < 3:
        return None, None, None, f"Invalid `lean_symbol` `{lean_symbol}` (must reside in a submodule under `Glamsterdam/`)"
    rel_cand = "/".join(parts[:-1]) + ".lean"
    resolved, canon_rel, err = resolve_safe_repo_file(rel_cand)
    if err is not None or resolved is None or canon_rel is None:
        return None, rel_cand, parts[-1], err or f"Missing Lean module file `{rel_cand}` for `{lean_symbol}`"
    return resolved, canon_rel, parts[-1], None


def extract_lean_slice(lean_file: pathlib.Path, short_sym: str, context_lines: int = 35) -> str:
    if "." in short_sym or not short_sym.strip():
        return ""
    lines = lean_file.read_text().splitlines()
    pat = re.compile(
        rf"^\s*(?:@\[.*?\]\s*)*(?:private\s+|protected\s+)?(?:def|theorem|structure|inductive|abbrev)\s+{re.escape(short_sym)}\b"
    )
    for idx, line in enumerate(lines):
        if pat.search(line):
            start = max(0, idx - 6)
            end = min(len(lines), idx + context_lines)
            return "\n".join(f"{i+1}: {lines[i]}" for i in range(start, end))
    return ""


def matches_scope(rel_path: str, scopes: list[str] | None) -> bool:
    if not scopes:
        return True
    return any(s in rel_path for s in scopes)


def validate_source_map_data(data: object, scopes: list[str] | None = None) -> tuple[list[str], list[dict]]:
    errors = []
    bundles = []
    if not isinstance(data, dict) or not isinstance(data.get("mappings"), list):
        return ["[source-map] Top-level YAML must be a mapping with a `mappings` list"], []
    for idx, entry in enumerate(data["mappings"]):
        if not isinstance(entry, dict):
            errors.append(f"[source-map] Entry #{idx} is not a mapping")
            continue
        lean_sym = entry.get("lean_symbol")
        upstream = entry.get("upstream")
        rel_path = entry.get("path")
        lines_spec = entry.get("lines")
        upstream_sym = entry.get("upstream_symbol")
        mapping_kind = entry.get("mapping_kind")

        if not isinstance(lean_sym, str) or not lean_sym.strip():
            errors.append(f"[source-map] Entry #{idx} has missing/invalid `lean_symbol`")
            continue
        if not isinstance(upstream, str) or not upstream.strip() or not isinstance(rel_path, str) or not rel_path.strip():
            errors.append(f"[source-map] {lean_sym}: missing/invalid `upstream` or `path`")
            continue
        if lines_spec is None or str(lines_spec).strip() == "":
            errors.append(f"[source-map] {lean_sym}: missing/invalid `lines`")
            continue

        # Global structural checks (always enforced even when --scope is set):
        # 1. Safe vendored upstream file resolution (no traversal, no symlinks)
        up_file, _, up_err = resolve_safe_vendor_file(f"{upstream}/{rel_path}")
        if up_err or up_file is None:
            errors.append(f"[source-map] Invalid vendored upstream path `{upstream}/{rel_path}` for {lean_sym}: {up_err}")
            continue
        # 2. Line range syntax and bounds check
        up_lines = up_file.read_text().splitlines()
        ranges, r_err = parse_line_ranges(str(lines_spec))
        if r_err:
            errors.append(f"[source-map] {r_err} in {rel_path} for {lean_sym}")
            continue
        up_slices = []
        for s, e in ranges:
            if s < 1 or e > len(up_lines) or s > e:
                errors.append(
                    f"[source-map] Out-of-bounds line range {s}-{e} (file has {len(up_lines)} lines) in {rel_path} for {lean_sym}"
                )
            else:
                chunk = "\n".join(f"{i}: {up_lines[i-1]}" for i in range(s, e + 1))
                up_slices.append(chunk)

        # 3. Safe Lean module path & exact declaration existence check (always enforced globally)
        lean_file, lean_rel, short_sym, lean_err = lean_module_to_path(lean_sym)
        if lean_err or lean_file is None or lean_rel is None or short_sym is None:
            errors.append(f"[source-map] Invalid Lean target for `{lean_sym}`: {lean_err}")
            continue
        lean_slice = extract_lean_slice(lean_file, short_sym)
        if not lean_slice:
            errors.append(f"[source-map] Symbol `{short_sym}` ({lean_sym}) not found in {lean_rel}")
            continue

        if not matches_scope(lean_rel, scopes):
            continue

        # Scoped semantic checks (enforced for all in-scope modules, and globally when unscoped):
        if not isinstance(upstream_sym, str) or not upstream_sym.strip():
            errors.append(f"[source-map] Missing required `upstream_symbol` for {lean_sym}")
        if mapping_kind not in ("exact", "projection"):
            errors.append(
                f"[source-map] Missing or invalid `mapping_kind` (must be 'exact' or 'projection') for {lean_sym}"
            )

        combined_up_slice = "\n...\n".join(up_slices)
        if isinstance(upstream_sym, str) and upstream_sym.strip() and combined_up_slice:
            sym_pat = re.compile(rf"\b{re.escape(upstream_sym)}\b")
            if not sym_pat.search(combined_up_slice):
                errors.append(
                    f"[source-map] Expected upstream_symbol `{upstream_sym}` (with identifier boundaries) NOT FOUND in {rel_path}:{lines_spec} for {lean_sym}"
                )

        bundles.append(
            {
                "lean_symbol": lean_sym,
                "lean_file": lean_rel,
                "mapping_kind": mapping_kind,
                "upstream_symbol": upstream_sym,
                "lean_slice": lean_slice,
                "upstream": upstream,
                "upstream_path": rel_path,
                "upstream_lines": str(lines_spec),
                "upstream_slice": combined_up_slice,
            }
        )
    return errors, bundles


def check_source_map(scopes: list[str] | None = None) -> tuple[list[str], list[dict]]:
    sm_path = ROOT / "audit" / "source-map.yaml"
    if not sm_path.exists() or sm_path.is_symlink() or not sm_path.is_file():
        return ["[source-map] Missing or invalid audit/source-map.yaml"], []
    data, y_err = safe_load_yaml_text(sm_path.read_text(), "source-map")
    if y_err:
        return [y_err], []
    return validate_source_map_data(data, scopes)


def check_inline_citations(
    v_index: dict[str, pathlib.Path], ambiguous: set[str], scopes: list[str] | None = None
) -> list[str]:
    errors = []
    cite_re = re.compile(r"`?([a-zA-Z0-9_./-]+\.(?:py|md)):(\d+)(?:-(\d+))?`?")
    header_re = re.compile(
        r"/--\s*(?:Exact\s+|Pure\s+|Stateful\s+)?`([a-zA-Z0-9_]+)`[^\n]*?\(`?([a-zA-Z0-9_./-]+\.(?:py|md)):(\d+)-(\d+)`?\)"
    )
    # Match markdown patterns like `` `func` (`path.py:s-e`) `` or `` `func` at `path.py:s-e` `` or `` `func:s-e` ``
    md_func_file_re = re.compile(
        r"`([a-z_][a-z0-9_]*)`\s*(?:\(|at\s+)`?([a-zA-Z0-9_./-]+\.(?:py|md)):(\d+)-(\d+)`?"
    )
    md_func_colon_re = re.compile(r"`([a-z_][a-z0-9_]*):(\d+)-(\d+)`")

    sm_data, _ = safe_load_yaml_text((ROOT / "audit" / "source-map.yaml").read_text(), "source-map")
    sym_to_files: dict[str, list[tuple[pathlib.Path, list[tuple[int, int]]]]] = {}
    if isinstance(sm_data, dict) and isinstance(sm_data.get("mappings"), list):
        for entry in sm_data["mappings"]:
            if isinstance(entry, dict):
                usym = entry.get("upstream_symbol")
                up = entry.get("upstream")
                rpath = entry.get("path")
                lspec = entry.get("lines")
                if isinstance(usym, str) and isinstance(up, str) and isinstance(rpath, str) and lspec is not None:
                    vf, _, _ = resolve_safe_vendor_file(f"{up}/{rpath}")
                    rngs, r_err = parse_line_ranges(str(lspec))
                    if vf is not None and not r_err:
                        sym_to_files.setdefault(usym, []).append((vf, rngs))

    def sym_matches_file_range(fn_sym: str, vf: pathlib.Path, s: int, e: int) -> bool:
        v_lines = vf.read_text().splitlines()
        ws = max(1, s - 2)
        we = min(len(v_lines), e + 2)
        if ws <= we and re.search(rf"\b{re.escape(fn_sym)}\b", "\n".join(v_lines[ws - 1 : we])):
            return True
        for mapped_vf, rngs in sym_to_files.get(fn_sym, []):
            if mapped_vf == vf:
                for ms, me in rngs:
                    if ms <= s and e <= me:
                        return True
        return False

    scan_files = (
        list((ROOT / "Glamsterdam").rglob("*.lean"))
        + list((ROOT / "audit").rglob("*.md"))
        + [ROOT / "README.md"]
    )
    for f in sorted(scan_files):
        rel = f.relative_to(ROOT).as_posix()
        if not matches_scope(rel, scopes):
            continue
        safe_f, _, s_err = resolve_safe_repo_file(rel)
        if s_err or safe_f is None:
            errors.append(f"[inline-citation] Unsafe scanned file `{rel}`: {s_err}")
            continue
        text = safe_f.read_text()
        for m in cite_re.finditer(text):
            fname, s_str, e_str = m.group(1), m.group(2), m.group(3)
            line_no = text[: m.start()].count("\n") + 1
            if fname in ambiguous:
                errors.append(
                    f"[inline-citation] {rel}:{line_no}: ambiguous upstream file suffix `{fname}` (specify directory prefix)"
                )
                continue
            if fname not in v_index:
                errors.append(
                    f"[inline-citation] {rel}:{line_no}: unknown upstream file `{fname}`"
                )
                continue
            v_file = v_index[fname]
            v_lines = v_file.read_text().splitlines()
            s = int(s_str)
            e = int(e_str) if e_str else s
            if s < 1 or e > len(v_lines) or s > e:
                errors.append(
                    f"[inline-citation] {rel}:{line_no}: out-of-bounds lines {s}-{e} for `{fname}` ({len(v_lines)} lines)"
                )

        if f.suffix == ".md":
            for mm in md_func_file_re.finditer(text):
                fn_sym, fname, s_str, e_str = mm.group(1), mm.group(2), mm.group(3), mm.group(4)
                line_no = text[: mm.start()].count("\n") + 1
                if fn_sym in sym_to_files and fname in v_index:
                    if not sym_matches_file_range(fn_sym, v_index[fname], int(s_str), int(e_str)):
                        errors.append(
                            f"[md-symbol-mismatch] {rel}:{line_no}: markdown cites `{fn_sym}` at `{fname}:{s_str}-{e_str}`, which neither contains `{fn_sym}` nor falls within its verified source-map range!"
                        )
            for mc in md_func_colon_re.finditer(text):
                fn_sym, s_str, e_str = mc.group(1), mc.group(2), mc.group(3)
                line_no = text[: mc.start()].count("\n") + 1
                cand_entries = sym_to_files.get(fn_sym, [])
                if cand_entries:
                    if not any(sym_matches_file_range(fn_sym, vf, int(s_str), int(e_str)) for vf, _ in cand_entries):
                        errors.append(
                            f"[md-symbol-mismatch] {rel}:{line_no}: markdown cites `{fn_sym}:{s_str}-{e_str}`, which neither contains `{fn_sym}` nor falls within its verified source-map range!"
                        )

        if f.suffix == ".lean":
            for hm in header_re.finditer(text):
                sym, fname, s_str, e_str = hm.group(1), hm.group(2), hm.group(3), hm.group(4)
                line_no = text[: hm.start()].count("\n") + 1
                if fname not in v_index:
                    continue
                v_lines = v_index[fname].read_text().splitlines()
                s = max(1, int(s_str) - 3)
                e = min(len(v_lines), int(e_str) + 3)
                window_text = "\n".join(v_lines[s - 1 : e])
                py_sym = sym[:-3] if sym.endswith("_tx") else sym
                if not re.search(rf"\b{re.escape(py_sym)}\b", window_text):
                    errors.append(
                        f"[docstring-symbol-mismatch] {rel}:{line_no}: docstring claims `{sym}` is at `{fname}:{s_str}-{e_str}`, but `{py_sym}` does not appear with identifier boundaries in those lines!"
                    )
    return errors


def check_banned_patterns(scopes: list[str] | None = None) -> list[str]:
    errors = []
    scan_paths = (
        list((ROOT / "Glamsterdam").rglob("*.lean"))
        + [p for p in (ROOT / "audit").rglob("*.yaml") if p.name != "remediation-ledger.yaml"]
        + list((ROOT / "audit").rglob("*.md"))
        + list((ROOT / "tests").rglob("*.py"))
    )
    for p in sorted(scan_paths):
        rel = p.relative_to(ROOT).as_posix()
        if not matches_scope(rel, scopes):
            continue
        safe_p, _, s_err = resolve_safe_repo_file(rel)
        if s_err or safe_p is None:
            errors.append(f"[banned-pattern] Unsafe scanned file `{rel}`: {s_err}")
            continue
        text = safe_p.read_text()
        for pat, reason in BANNED_PATTERNS:
            for m in re.finditer(pat, text):
                line_no = text[: m.start()].count("\n") + 1
                errors.append(f"[banned-pattern] {rel}:{line_no}: matched `{m.group(0)}` -> {reason}")
    return errors


def run_self_tests() -> list[str]:
    import quorum_gate

    failures = []
    # 1. Path traversal / absolute path tests
    for bad_path in ["/etc/passwd", "../outside.py", "execution_specs/../../outside.py", ""]:
        p, _, err = resolve_safe_vendor_file(bad_path)
        if p is not None or err is None:
            failures.append(f"Self-test failed: resolve_safe_vendor_file accepted unsafe path `{bad_path}`")
        rp, _, rerr = resolve_safe_repo_file(bad_path)
        if rp is not None or rerr is None:
            failures.append(f"Self-test failed: resolve_safe_repo_file accepted unsafe path `{bad_path}`")

    # 2. Symlink rejection test (both leaf symlinks and symlinked parent directories inside ROOT and VENDOR_DIR)
    with tempfile.TemporaryDirectory(dir=ROOT) as tmpd:
        tmp_path = pathlib.Path(tmpd)
        sym_target = ROOT / "README.md"
        sym_link = tmp_path / "symlink_test.md"
        sym_link.symlink_to(sym_target)
        rel_sym = sym_link.relative_to(ROOT).as_posix()
        rp, _, rerr = resolve_safe_repo_file(rel_sym)
        if rp is not None or rerr is None or "Symlink component" not in rerr:
            failures.append(f"Self-test failed: resolve_safe_repo_file did not reject leaf symlink `{rel_sym}`")

        sym_dir = tmp_path / "linked_glamsterdam"
        sym_dir.symlink_to(ROOT / "Glamsterdam")
        rel_nested = (sym_dir / "Common" / "Prelude.lean").relative_to(ROOT).as_posix()
        rp2, _, rerr2 = resolve_safe_repo_file(rel_nested)
        if rp2 is not None or rerr2 is None or "Symlink component" not in rerr2:
            failures.append(f"Self-test failed: resolve_safe_repo_file did not reject symlinked parent directory `{rel_nested}`")

    with tempfile.TemporaryDirectory(dir=VENDOR_DIR) as vtmpd:
        vtmp_path = pathlib.Path(vtmpd)
        vsym_dir = vtmp_path / "linked_eips"
        vsym_dir.symlink_to(VENDOR_DIR / "eips")
        vrel_nested = (vsym_dir / "EIPS" / "eip-7732.md").relative_to(VENDOR_DIR).as_posix()
        vp, _, verr = resolve_safe_vendor_file(vrel_nested)
        if vp is not None or verr is None or "Symlink component" not in verr:
            failures.append(f"Self-test failed: resolve_safe_vendor_file did not reject symlinked parent directory `{vrel_nested}`")

        vsym_file = vtmp_path / "linked_fork.py"
        vsym_file.symlink_to(VENDOR_DIR / "execution_specs/src/ethereum/forks/amsterdam/fork.py")
        v_idx, _ = build_vendored_file_index()
        if "linked_fork.py" in v_idx or any("linked_eips" in k for k in v_idx):
            failures.append("Self-test failed: build_vendored_file_index included symlinked file or directory")

        fifo_path = vtmp_path / "unlisted_fifo.pipe"
        os.mkfifo(fifo_path)
        sha_errs, _ = check_sha256sums()
        if not any("Forbidden non-regular entry" in e for e in sha_errs):
            failures.append("Self-test failed: check_sha256sums did not reject unlisted FIFO in vendor/upstreams")

        sm_sym_errs, _ = validate_source_map_data(
            {
                "mappings": [
                    {
                        "lean_symbol": "Glamsterdam.Common.Prelude.Address",
                        "upstream": vtmp_path.relative_to(VENDOR_DIR).as_posix(),
                        "path": "linked_eips/EIPS/eip-7732.md",
                        "lines": "1-5",
                    }
                ]
            },
            scopes=["NonMatchingScope"],
        )
        if not sm_sym_errs or not any("Symlink component" in e for e in sm_sym_errs):
            failures.append("Self-test failed: validate_source_map_data did not globally reject symlinked parent directory under --scope")

    # 2b. Vendored suffix collision detection test (both orders: a/b.py vs b.py)
    dummy_p1 = VENDOR_DIR / "a/b.py"
    dummy_p2 = VENDOR_DIR / "b.py"
    for order in [{"a/b.py": dummy_p1, "b.py": dummy_p2}, {"b.py": dummy_p2, "a/b.py": dummy_p1}]:
        c_idx, c_amb = index_vendored_rel_paths(order)
        if "b.py" not in c_amb or "b.py" in c_idx:
            failures.append("Self-test failed: index_vendored_rel_paths failed to detect collision between `a/b.py` and `b.py`")

    # 2c. Malformed / escaping / multi-suffix lean_symbol tests
    for bad_sym in [
        "../../etc/passwd.foo",
        "Glamsterdam..Foo",
        "NotGlamsterdam.Foo.bar",
        "SingleToken",
        "Glamsterdam.NonExistentMod.sym",
        "Glamsterdam.Common.Prelude.Address.garbage",
    ]:
        lf, _, _, lerr = lean_module_to_path(bad_sym)
        if lf is not None or lerr is None:
            failures.append(f"Self-test failed: lean_module_to_path accepted invalid/missing lean_symbol `{bad_sym}`")

    sm_missing_decl_errs, _ = validate_source_map_data(
        {
            "mappings": [
                {
                    "lean_symbol": "Glamsterdam.Common.Prelude.NonExistentDecl",
                    "upstream": "eips",
                    "path": "EIPS/eip-7732.md",
                    "lines": "1-5",
                }
            ]
        },
        scopes=["NonMatchingScope"],
    )
    if not sm_missing_decl_errs or not any("not found in" in e for e in sm_missing_decl_errs):
        failures.append("Self-test failed: validate_source_map_data did not globally reject missing Lean declaration")

    # 3. Malformed line range tests
    for bad_range in ["", "abc", "10-abc", "12-15,foo"]:
        rng, rerr = parse_line_ranges(bad_range)
        if rerr is None:
            failures.append(f"Self-test failed: parse_line_ranges accepted malformed range `{bad_range}`")
    rng, rerr = parse_line_ranges("10-12,20")
    if rerr is not None or rng != [(10, 12), (20, 20)]:
        failures.append("Self-test failed: parse_line_ranges failed on valid range `10-12,20`")

    # 4. Malformed YAML crash-resilience test
    _, yerr = safe_load_yaml_text("items: [unclosed: {yaml", "test-yaml")
    if yerr is None or "Malformed YAML" not in yerr:
        failures.append("Self-test failed: safe_load_yaml_text did not catch malformed YAML")

    # 5. Ledger schema violation tests (wrong IDs, wrong cardinality, missing fields, non-string description)
    for bad_ledger in [
        {"schema_version": 2, "items": []},
        {"schema_version": 1, "description": "", "items": []},
        {"schema_version": 1, "description": "desc", "items": [{"id": "WRONG-ID"} for _ in range(6)]},
    ]:
        l_errs, _ = validate_ledger_data(bad_ledger)
        if not l_errs:
            failures.append(f"Self-test failed: validate_ledger_data accepted invalid ledger `{bad_ledger}`")

    # 6. Malformed source-map entry tests
    for bad_sm in [
        ["not-a-dict"],
        {"mappings": ["not-a-dict"]},
        {"mappings": [{"lean_symbol": "", "upstream": "execution_specs", "path": "foo.py", "lines": "1-2"}]},
        {"mappings": [{"lean_symbol": "Glamsterdam.Common.Prelude.Address", "upstream": "", "path": "", "lines": ""}]},
    ]:
        sm_errs, _ = validate_source_map_data(bad_sm)
        if not sm_errs:
            failures.append(f"Self-test failed: validate_source_map_data accepted malformed input `{bad_sm}`")

    # 7. Quorum gate verdict & failure handling tests (including mid-stream markers and non-empty stderr)
    if quorum_gate.evaluate_verdict(1, "VERDICT: PASS"):
        failures.append("Self-test failed: evaluate_verdict accepted nonzero returncode")
    if quorum_gate.evaluate_verdict(0, "VERDICT: PASS", "ssh operational warning on stderr"):
        failures.append("Self-test failed: evaluate_verdict accepted non-empty stderr")
    if quorum_gate.evaluate_verdict(0, "warning\nSUBPROCESS_ERROR: TimeoutExpired\nVERDICT: PASS"):
        failures.append("Self-test failed: evaluate_verdict accepted mid-text SUBPROCESS_ERROR output")
    if quorum_gate.evaluate_verdict(0, "some prefix\nHTTP_ERROR: 500\nVERDICT: PASS"):
        failures.append("Self-test failed: evaluate_verdict accepted mid-text HTTP_ERROR output")
    if quorum_gate.evaluate_verdict(0, "Previously we saw VERDICT: PASS, but now:\nVERDICT: FAIL"):
        failures.append("Self-test failed: evaluate_verdict failed to reject final VERDICT: FAIL")
    if not quorum_gate.evaluate_verdict(0, "Previously we saw VERDICT: FAIL in round 1.\nNow:\nVERDICT: PASS"):
        failures.append("Self-test failed: evaluate_verdict rejected valid final VERDICT: PASS")

    return failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dump-bundle", help="Filter substring for lean_file to dump side-by-side bundle JSON")
    ap.add_argument("--json-out", help="Write bundle JSON to path")
    ap.add_argument("--scope", action="append", help="Restrict verification to files matching substring(s)")
    ap.add_argument(
        "--enforce-ledger-step",
        action="append",
        help="Enforce required/forbidden symbols for remediation ledger step(s) (e.g. step2, step3, step4, all)",
    )
    ap.add_argument("--self-test", action="store_true", help="Run adversarial self-tests on path/range validators")
    args = ap.parse_args()

    if args.self_test:
        st_failures = run_self_tests()
        if st_failures:
            for f in st_failures:
                print(f"  - {f}", file=sys.stderr)
            return 1
        print(
            "verify_ground_truth --self-test OK: all 7 adversarial test suites "
            "(path traversal, symlinks, line ranges, malformed YAML, ledger schema, source-map schema, quorum verdict) passed."
        )
        return 0

    v_index, ambiguous = build_vendored_file_index()
    sha_errors, sha_count = check_sha256sums()
    ledger_errors, ledger_count = check_remediation_ledger(args.enforce_ledger_step)
    sm_errors, bundles = check_source_map(args.scope)
    cite_errors = check_inline_citations(v_index, ambiguous, args.scope)
    pat_errors = check_banned_patterns(args.scope)

    if args.dump_bundle is not None:
        filtered = [b for b in bundles if args.dump_bundle in b["lean_file"]]
        out_str = json.dumps(filtered, indent=2)
        if args.json_out:
            pathlib.Path(args.json_out).write_text(out_str)
        else:
            print(out_str)

    all_errors = sha_errors + ledger_errors + sm_errors + cite_errors + pat_errors
    if all_errors:
        print(f"verify_ground_truth FAILED with {len(all_errors)} error(s):", file=sys.stderr)
        for err in all_errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    scope_label = f" (scope={args.scope})" if args.scope else ""
    print(
        f"verify_ground_truth OK{scope_label}: {sha_count} canonical vendored SHA256SUMS verified, "
        f"{ledger_count} remediation-ledger items verified, "
        f"{len(bundles)} source mappings verified, inline citations verified, 0 banned hallucination patterns."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
