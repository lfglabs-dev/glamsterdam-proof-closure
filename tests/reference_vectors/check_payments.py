"""Compare the pinned official Gloas builder-payment handler with compiled Lean."""
import argparse
import ctypes
import hashlib
import importlib
import json
import subprocess
import tarfile
import tempfile
from pathlib import Path

import snappy

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SPEC = "aa16bb4c156184e9548a997d53efaf2a228a6304"
ARCHIVES = {
    "minimal": "26d09aea70c62ed235a120a95082d544ab1c2e6fe36bd35ea1bd5da62f3b7b68",
    "mainnet": "67762986572372a08d3b182535aa760433c86e174e14e0bbd756f350dd19398c",
}


def compile_bridge(directory):
    subprocess.run(["lake", "build", "Glamsterdam.Gloas7732.Spec"], cwd=ROOT, check=True)
    generated = directory / "PaymentVectors.c"
    subprocess.run(["lake", "env", "lean", "-c", generated, "tests/reference_vectors/PaymentVectors.lean"],
                   cwd=ROOT, check=True)
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    runtime = prefix / "lib/lean"
    ir = ROOT / ".lake/build/ir/Glamsterdam"
    so = directory / "payments.so"
    subprocess.run(["cc", "-O2", "-fPIC", "-shared", f"-I{prefix / 'include'}",
                    HERE / "bridge.c", generated, ir / "Common/Prelude.c", ir / "Common/MetaSpec.c",
                    ir / "Gloas7732/Spec.c", f"-L{runtime}", "-lleanshared",
                    f"-Wl,-rpath,{runtime}", "-o", so], check=True)
    lib = ctypes.CDLL(str(so))
    lib.initialize_vectors.argtypes = []
    lib.initialize_vectors.restype = ctypes.c_int
    if lib.initialize_vectors():
        raise RuntimeError("Lean initialization failed")
    lib.replay_vectors.argtypes = [ctypes.c_char_p]
    lib.replay_vectors.restype = ctypes.c_void_p
    lib.release_output.argtypes = [ctypes.c_void_p]
    lib.release_output.restype = None
    return lib


def read_cases(preset, archive):
    with archive.open("rb") as file:
        digest = hashlib.file_digest(file, "sha256").hexdigest()
    if digest != ARCHIVES[preset]:
        raise ValueError(f"{archive}: unexpected SHA-256 {digest}")
    prefix = f"tests/{preset}/gloas/epoch_processing/builder_pending_payments/"
    cases = {}
    with tarfile.open(archive, "r|gz") as tar:
        for member in tar:
            if not member.name.startswith(prefix):
                continue
            parts = member.name.removeprefix(prefix).rstrip("/").split("/")
            if len(parts) >= 2:
                case = cases.setdefault("/".join(parts[:2]), {})
                if len(parts) == 3 and parts[2] in {"pre.ssz_snappy", "post.ssz_snappy"}:
                    if parts[2] in case or not member.isfile():
                        raise ValueError(f"unexpected fixture entry {member.name}")
                    case[parts[2]] = tar.extractfile(member).read()
    if not cases:
        raise ValueError(f"no {preset} builder-payment cases discovered")
    return cases


def withdrawal(w):
    return {"feeRecipient": int.from_bytes(bytes(w.fee_recipient), "big"),
            "amount": int(w.amount), "builderIndex": int(w.builder_index)}


def queues(state):
    return {"payments": [{"weight": int(p.weight), "proposerIndex": int(p.proposer_index),
                          "withdrawal": withdrawal(p.withdrawal)} for p in state.builder_pending_payments],
            "withdrawals": [withdrawal(w) for w in state.builder_pending_withdrawals]}


def replay(lib, data):
    ptr = lib.replay_vectors(json.dumps(data).encode())
    if not ptr:
        raise MemoryError("could not allocate result")
    try:
        return json.loads(ctypes.string_at(ptr))
    finally:
        lib.release_output(ptr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archives", type=Path)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    report = {"spec": SPEC, "proof_commit": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "handler": "gloas/epoch_processing/builder_pending_payments",
        "fields": ["builder_pending_payments", "builder_pending_withdrawals"], "presets": {}}
    failed = 0
    with tempfile.TemporaryDirectory() as tmp:
        lib = compile_bridge(Path(tmp))
        for preset, digest in ARCHIVES.items():
            spec = importlib.import_module(f"eth_consensus_specs.gloas.{preset}")
            decoder_revision = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=Path(spec.__file__).parent, text=True).strip()
            if decoder_revision != SPEC:
                raise ValueError(f"{preset}: decoder checkout is {decoder_revision}, expected {SPEC}")
            cases = read_cases(preset, args.archives / f"{preset}.tar.gz")
            results = {}
            for name, case in sorted(cases.items()):
                try:
                    pre, post = [spec.BeaconState.decode_bytes(snappy.decompress(case[key]))
                                 for key in ("pre.ssz_snappy", "post.ssz_snappy")]
                    data = queues(pre)
                    data.update(totalActiveBalance=int(spec.get_total_active_balance(pre)),
                                slotsPerEpoch=int(spec.SLOTS_PER_EPOCH))
                    actual = replay(lib, data)
                    for field, expected in queues(post).items():
                        if actual[field] != expected:
                            index = next((i for i, (a, b) in enumerate(zip(actual[field], expected))
                                          if a != b), min(len(actual[field]), len(expected)))
                            raise ValueError(f"{field}[{index}] expected {expected[index:index+1]}, "
                                             f"got {actual[field][index:index+1]}")
                    results[name] = "passed"
                except Exception as exc:
                    results[name] = f"failed: {exc!r}"
                    failed += 1
            passed = sum(result == "passed" for result in results.values())
            report["presets"][preset] = {"archive_sha256": digest, "passed": passed,
                                         "discovered": len(cases), "cases": results}
            print(f"{preset}: {passed}/{len(cases)}")
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    if failed:
        raise SystemExit(f"{failed} cases failed; see {args.report}")


if __name__ == "__main__":
    main()
