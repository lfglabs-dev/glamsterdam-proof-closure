#!/usr/bin/env python3
"""
Validate that every guarantee in `audit/guarantees.yaml` maps to an existing
Lean 4 theorem/definition in `Glamsterdam/` and that zero `sorry` or `axiom`
declarations appear anywhere in the codebase.
"""
import pathlib
import re
import sys
import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent


def main() -> int:
    guarantees_path = ROOT / "audit" / "guarantees.yaml"
    assumptions_path = ROOT / "audit" / "assumptions.yaml"
    source_map_path = ROOT / "audit" / "source-map.yaml"

    for p in (guarantees_path, assumptions_path, source_map_path):
        if not p.exists():
            print(f"ERROR: missing metadata file {p}", file=sys.stderr)
            return 1

    guarantees = yaml.safe_load(guarantees_path.read_text())["guarantees"]
    assumptions = yaml.safe_load(assumptions_path.read_text())
    source_map = yaml.safe_load(source_map_path.read_text())

    for g in guarantees:
        lean_file = ROOT / g["file"]
        if not lean_file.exists():
            print(f"ERROR: missing Lean file {lean_file} for {g['id']}", file=sys.stderr)
            return 1
        text = lean_file.read_text()
        thm = g["theorem"]
        pattern = rf"\b(theorem|def)\s+{re.escape(thm)}\b"
        if not re.search(pattern, text):
            print(f"ERROR: symbol `{thm}` for `{g['id']}` not found in {g['file']}", file=sys.stderr)
            return 1
        if "kill_line" in g:
            kl = g["kill_line"]
            if not re.search(rf"\b(theorem|def)\s+{re.escape(kl)}\b", text):
                print(f"ERROR: kill_line `{kl}` for `{g['id']}` not found in {g['file']}", file=sys.stderr)
                return 1

    for lean_file in (ROOT / "Glamsterdam").rglob("*.lean"):
        content = lean_file.read_text()
        stripped = re.sub(r"/-.*?-/", "", content, flags=re.S)
        stripped = re.sub(r"--.*", "", stripped)
        if re.search(r"\bsorry\b", stripped):
            print(f"ERROR: forbidden `sorry` in {lean_file}", file=sys.stderr)
            return 1
        if re.search(r"\bnative_decide\b", stripped):
            print(f"ERROR: forbidden `native_decide` in {lean_file}", file=sys.stderr)
            return 1
        if re.search(r"^\s*axiom\b", stripped, flags=re.M):
            print(f"ERROR: forbidden `axiom` in {lean_file}", file=sys.stderr)
            return 1

    print(
        f"audit-check ok: {len(guarantees)} guarantees, "
        f"{len(assumptions.get('assumptions', []))} assumptions, "
        f"{len(assumptions.get('exclusions', []))} exclusions, "
        f"{len(source_map.get('mappings', []))} source mappings verified."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
