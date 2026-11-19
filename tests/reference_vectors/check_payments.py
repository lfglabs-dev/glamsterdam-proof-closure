"""Compare the pinned official Gloas builder-payment handler with compiled Lean."""
from collections import Counter, defaultdict
import argparse
import ctypes
import hashlib
import importlib
import json
import os
import sys
import subprocess
import tarfile
import tempfile
from pathlib import Path

import snappy

from inventory import inventory
from static_ssz import check_archive, check_codec_controls

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SPEC = "aa16bb4c156184e9548a997d53efaf2a228a6304"
HANDLERS = {
    "epoch_processing/builder_pending_payments",
    "operations/builder_deposit_request",
    "operations/builder_exit_request",
}


def compile_bridge(directory):
    subprocess.run(["lake", "build", "Glamsterdam.Gloas7732.BuilderRequests"], cwd=ROOT, check=True)
    generated = directory / "PaymentVectors.c"
    subprocess.run(["lake", "env", "lean", "-c", generated, "tests/reference_vectors/PaymentVectors.lean"],
                   cwd=ROOT, check=True)
    ssz_c = directory / "Ssz.c"
    subprocess.run(["lake", "env", "lean", "-c", ssz_c, "tests/reference_vectors/Ssz.lean"],
                   cwd=ROOT, check=True)
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    runtime = prefix / "lib/lean"
    ir = ROOT / ".lake/build/ir/Glamsterdam"
    so = directory / "payments.so"
    subprocess.run(["cc", "-O2", "-fPIC", "-shared", f"-I{prefix / 'include'}",
                    HERE / "bridge.c", HERE / "ssz_bridge.c", ssz_c, generated, ir / "Common/Prelude.c", ir / "Common/MetaSpec.c",
                    ir / "Gloas7732/Spec.c", ir / "Gloas7732/BuilderRequests.c", f"-L{runtime}", "-lleanshared",
                    f"-Wl,-rpath,{runtime}", "-o", so], check=True)
    lib = ctypes.CDLL(str(so))
    lib.initialize_vectors.argtypes = []
    lib.initialize_vectors.restype = ctypes.c_int
    if lib.initialize_vectors():
        raise RuntimeError("Lean initialization failed")
    lib.initialize_ssz_vectors.argtypes = []
    lib.initialize_ssz_vectors.restype = ctypes.c_int
    if lib.initialize_ssz_vectors():
        raise RuntimeError("Lean SSZ initialization failed")
    lib.ssz_vector_root.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_size_t]
    lib.ssz_vector_root.restype = ctypes.c_void_p
    lib.replay_vectors.argtypes = [ctypes.c_char_p]
    lib.replay_vectors.restype = ctypes.c_void_p
    lib.release_output.argtypes = [ctypes.c_void_p]
    lib.release_output.restype = None
    return lib


def read_cases(archive, selected):
    cases = {name: {} for name in selected}
    with tarfile.open(archive, "r|gz") as tar:
        for member in tar:
            path = member.name.removeprefix("tests/").split("/")
            name = "/".join(path[:-1])
            if name not in cases or not member.isfile() or not path[-1].endswith(".ssz_snappy"):
                continue
            if path[-1] in {"pre_epoch.ssz_snappy", "post_epoch.ssz_snappy"}:
                continue
            if path[-1] in cases[name]:
                raise ValueError(f"duplicate fixture file: {member.name}")
            cases[name][path[-1]] = tar.extractfile(member).read()
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


def builder(b):
    return {"pubkey": int.from_bytes(bytes(b.pubkey), "big"), "version": int(b.version),
            "executionAddress": int.from_bytes(bytes(b.execution_address), "big"),
            "balance": int(b.balance), "depositEpoch": int(b.deposit_epoch),
            "withdrawableEpoch": int(b.withdrawable_epoch)}


def decode_withdrawal(spec, w):
    return spec.BuilderPendingWithdrawal(fee_recipient=w["feeRecipient"].to_bytes(20, "big"),
                                         amount=w["amount"], builder_index=w["builderIndex"])


def apply_output(spec, state, handler, actual):
    if handler == "builder_pending_payments":
        state.builder_pending_payments = type(state.builder_pending_payments)(data=[
            spec.BuilderPendingPayment(weight=p["weight"], proposer_index=p["proposerIndex"],
                                       withdrawal=decode_withdrawal(spec, p["withdrawal"]))
            for p in actual["payments"]])
        state.builder_pending_withdrawals = type(state.builder_pending_withdrawals)(data=[
            decode_withdrawal(spec, w) for w in actual["withdrawals"]])
    else:
        state.builders = spec.Builders(data=[spec.Builder(pubkey=b["pubkey"].to_bytes(48, "big"),
            version=b["version"], execution_address=b["executionAddress"].to_bytes(20, "big"),
            balance=b["balance"], deposit_epoch=b["depositEpoch"], withdrawable_epoch=b["withdrawableEpoch"])
            for b in actual["builders"]])


def check_case(lib, spec, name, case):
    handler = name.split("/")[3]
    def decoded(field, typ):
        return typ.decode_bytes(snappy.decompress(case[field + ".ssz_snappy"]))
    pre = decoded("pre", spec.BeaconState)
    data = queues(pre)
    data.update(handler=handler, slot=int(pre.slot), slotsPerEpoch=int(spec.SLOTS_PER_EPOCH))
    if handler == "builder_pending_payments":
        data.update(increment=int(spec.EFFECTIVE_BALANCE_INCREMENT), validators=[
            dict(activationEpoch=int(v.activation_epoch), exitEpoch=int(v.exit_epoch),
                 effectiveBalance=int(v.effective_balance)) for v in pre.validators])
    else:
        data.update(builders=[builder(b) for b in pre.builders],
                    delay=int(spec.config.MIN_BUILDER_WITHDRAWABILITY_DELAY))
        if handler == "builder_exit_request":
            request = decoded(handler, spec.BuilderExitRequest)
            data.update(source=int.from_bytes(bytes(request.source_address), "big"),
                        finalized=int(pre.finalized_checkpoint.epoch))
        else:
            request = decoded(handler, spec.BuilderDepositRequest)
            data.update(prefix=request.withdrawal_credentials[0], amount=int(request.amount))
        data["pubkey"] = int.from_bytes(bytes(request.pubkey), "big")
    actual = replay(lib, data)
    if "unsupported" in actual:
        return {"status": "unsupported", "dependency": actual["unsupported"]}
    expected = decoded("post", spec.BeaconState)
    control = None
    if name.endswith("/process_builder_pending_payments_queue_rotation"):
        half = int(spec.SLOTS_PER_EPOCH)
        wrong = {**actual, "payments": actual["payments"][half:] + actual["payments"][:half]}
        mutated = pre.model_copy(deep=True)
        apply_output(spec, mutated, handler, wrong)
        if mutated.hash_tree_root() == expected.hash_tree_root():
            raise AssertionError("rotation control survived")
        control = "swapped epoch halves detected"
    if name.endswith(("/process_builder_exit_request__success", "/process_builder_deposit_request__top_up")):
        if pre.hash_tree_root() == expected.hash_tree_root():
            raise AssertionError("dropped registry update control survived")
        control = "missing registry update detected"
    apply_output(spec, pre, handler, actual)
    if pre.encode_bytes() != expected.encode_bytes():
        field = next(f for f in spec.BeaconState.model_fields if getattr(pre, f) != getattr(expected, f))
        raise ValueError(f"first differing BeaconState field: {field}")
    return {"status": "full_pass", **({"negative_control": control} if control else {})}


DEPENDENCIES = {
    "ssz_static": "Lean SSZ codec and hash-tree-root for the fixture type",
    "fork_choice": "fork-choice store, event processing and head selection",
    "fork": "complete fork upgrade, including registry onboarding and all initialized state",
    "transition": "full beacon-block processing across the fork boundary",
    "networking": "Gloas gossip validation, cryptography and networking context",
    "fast_confirmation": "fast-confirmation rules and fork-choice history",
    "finality": "full block and epoch transitions with finality",
    "light_client": "light-client state machine and sync committee verification",
    "sanity": "full slot/block state transition",
    "random": "full block sequence state transition",
    "rewards": "full validator participation, reward and penalty accounting",
    "operations": "complete pinned operation and its validation rules",
    "epoch_processing": "complete pinned epoch sub-transition",
}


def fingerprint(ids):
    return hashlib.sha256(("\n".join(sorted(ids)) + "\n").encode()).hexdigest()


def collect_sources(directory):
    module = importlib.import_module("eth_consensus_specs.gloas.minimal")
    cwd = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"],
                                      cwd=Path(module.__file__).parent, text=True).strip())
    if subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=cwd, text=True).strip() != SPEC:
        raise ValueError("generator checkout does not match the pinned release")
    output = directory / "sources.json"
    env = {**os.environ, "GLOAS_SOURCE_CATALOG": str(output), "PYTHONPATH": str(HERE)}
    subprocess.run([sys.executable, "-m", "pytest", "--collect-only", "--reftests",
                    "--fork=gloas", "--preset=minimal", "--preset=mainnet", "-p", "generator_sources",
                    "-q", "tests/core/pyspec/eth_consensus_specs/test"], cwd=cwd, env=env,
                   stdout=subprocess.DEVNULL, check=True)
    sources = defaultdict(set)
    units = set()
    for row in json.loads(output.read_text()):
        if "case" in row:
            sources[row["case"]].add(row["source"])
        else:
            units.add(row["python_only"])
    return sources, sorted(units)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archives", type=Path)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    archives, cases = inventory(args.archives)
    report = {"spec": SPEC, "proof_commit": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(), "archives": archives,
        "case_id_sha256": fingerprint(cases), "cases": {}}
    results = report["cases"]
    with tempfile.TemporaryDirectory() as tmp:
        sources, report["gloas_python_only"] = collect_sources(Path(tmp))
        lib = compile_bridge(Path(tmp))
        report["ssz_controls"] = check_codec_controls(lib)
        for preset in ("minimal", "mainnet"):
            spec = importlib.import_module(f"eth_consensus_specs.gloas.{preset}")
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                               cwd=Path(spec.__file__).parent, text=True).strip()
            if revision != SPEC:
                raise ValueError(f"{preset}: unexpected PySpec revision {revision}")
            selected = []
            static = set()
            for name, scope in cases.items():
                config, _, runner, handler, _, _ = name.split("/")
                if config != preset:
                    continue
                if scope == "compliance":
                    results[name] = {"status": "separate_compliance"}
                elif runner == "ssz_static":
                    static.add(name)
                elif f"{runner}/{handler}" in HANDLERS:
                    selected.append(name)
                else:
                    results[name] = {"status": "unsupported", "dependency": DEPENDENCIES[runner]}
            check_archive(lib, spec, args.archives / f"{preset}.tar.gz", static, results)
            for name, case in read_cases(args.archives / f"{preset}.tar.gz", selected).items():
                try:
                    results[name] = check_case(lib, spec, name, case)
                except Exception as exc:
                    results[name] = {"status": "failed", "error": repr(exc)}
    if set(results) != set(cases):
        raise ValueError("missing or unexpected inventory results")
    for name, scope in cases.items():
        if scope == "reference":
            if not sources[name]:
                raise ValueError(f"no matching pinned generator candidate for {name}")
            results[name]["generator_candidates"] = sorted(sources[name])
    report["counts"] = dict(Counter(r["status"] for r in results.values()))
    print(report["counts"])
    args.report.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    baselines = {status: fingerprint(k for k, r in results.items() if r["status"] == status)
                 for status in report["counts"]}
    if "failed" in baselines or baselines != json.loads((HERE / "coverage-baseline.json").read_text()):
        raise SystemExit("coverage differs from reviewed baseline; inspect per-case report")


if __name__ == "__main__":
    main()
