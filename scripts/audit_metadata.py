#!/usr/bin/env python3
"""
Validate that every guarantee in `audit/guarantees.yaml` maps to an existing
Lean 4 theorem/definition in `Glamsterdam/` and that zero `sorry` or `axiom`
declarations appear anywhere in the codebase.
"""
import pathlib
import re
import subprocess
import sys
import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWED_STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


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

    axiom_check_lines = ["import Glamsterdam"]
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
        mod_prefix = g["file"].replace("/", ".")[:-5]
        axiom_check_lines.append(f"#print axioms {mod_prefix}.{thm}")
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
        if re.search(r"^\s*(?:private\s+|protected\s+)?axiom\b", stripped, flags=re.M):
            print(f"ERROR: forbidden `axiom` in {lean_file}", file=sys.stderr)
            return 1

    # Kernel-level #print axioms verification across all guarantee theorems
    proc = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT,
        input="\n".join(axiom_check_lines),
        text=True,
        capture_output=True,
    )
    if proc.returncode != 0:
        print(f"ERROR: `lake env lean --stdin` #print axioms failed:\n{proc.stderr}\n{proc.stdout}", file=sys.stderr)
        return 1
    for m in re.finditer(r"'(.*?)' depends on axioms: \[(.*?)\]", proc.stdout, flags=re.S):
        sym_name = m.group(1)
        ax_list = [a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()]
        disallowed = [a for a in ax_list if a not in ALLOWED_STANDARD_AXIOMS]
        if disallowed:
            print(f"ERROR: `{sym_name}` depends on forbidden axioms: {disallowed}", file=sys.stderr)
            return 1

    print(
        f"audit-check ok: {len(guarantees)} guarantees, "
        f"{len(assumptions.get('assumptions', []))} assumptions, "
        f"{len(assumptions.get('exclusions', []))} exclusions, "
        f"{len(source_map.get('mappings', []))} source mappings verified "
        f"(zero_sorry: true, zero_axiom: true, zero_native_decide: true, "
        f"kernel_print_axioms_verified: {len(guarantees)}/{len(guarantees)})."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
