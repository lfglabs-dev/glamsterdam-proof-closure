"""Enumerate the tagged release, independently of which Lean handlers exist."""
import hashlib
import subprocess
from pathlib import Path

ARCHIVES = {
    "minimal": "26d09aea70c62ed235a120a95082d544ab1c2e6fe36bd35ea1bd5da62f3b7b68",
    "mainnet": "67762986572372a08d3b182535aa760433c86e174e14e0bbd756f350dd19398c",
    "general": "c4f395f71f606c28093500e32067990e430cc73a2277be6f3bf5090adcce3f67",
    "comptests": "ccb3149d29e4179e852499f1a3d121424dbac22745375908cd9059350aece746",
}


def inventory(directory: Path):
    cases = {}
    archives = {}
    for archive, digest in ARCHIVES.items():
        path = directory / f"{archive}.tar.gz"
        with path.open("rb") as file:
            if hashlib.file_digest(file, "sha256").hexdigest() != digest:
                raise ValueError(f"{path}: incorrect release digest")
        dirs, manifests, payloads = set(), set(), set()
        with subprocess.Popen(["tar", "tzf", path], stdout=subprocess.PIPE, text=True) as tar:
            for line in tar.stdout:
                parts = line.rstrip("\n").split("/")
                if len(parts) < 8 or parts[0] != "tests" or parts[1] not in (
                    "minimal", "mainnet", "general"
                ) or parts[2] != "gloas":
                    continue
                case = "/".join(parts[1:7])
                if parts[7:] == [""]:
                    dirs.add(case)
                elif parts[7:] == ["manifest.yaml"]:
                    if case in manifests:
                        raise ValueError(f"duplicate case manifest: {case}")
                    manifests.add(case)
                elif parts[-1]:
                    payloads.add(case)
            if tar.wait():
                raise ValueError(f"could not read {path}")
        if dirs != manifests or manifests != payloads:
            raise ValueError(f"{archive}: case directories, manifests and payloads disagree")
        scope = "compliance" if archive == "comptests" else "reference"
        for case in manifests:
            if case in cases:
                raise ValueError(f"duplicate release case: {case}")
            cases[case] = scope
        archives[archive] = dict(sha256=digest, count=len(manifests), scope=scope)
    return archives, dict(sorted(cases.items()))
