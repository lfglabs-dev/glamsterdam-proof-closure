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

from ruamel.yaml import YAML
import snappy

from inventory import inventory
from screen import screen_cases, screen_blocks, screen_state
from payment_histories import replay_history, equal_amount_history
from boundary_checks import additional_checks
from claim_sources import source_manifest
from static_ssz import check_archive, check_codec_controls

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SPEC = "aa16bb4c156184e9548a997d53efaf2a228a6304"
HANDLERS = {
    "epoch_processing/builder_pending_payments",
    "operations/builder_deposit_request",
    "operations/builder_exit_request",
    "operations/payload_attestation",
    "operations/parent_execution_payload",
    "operations/execution_payload_bid",
    "operations/attestation",
}


def compile_bridge(directory):
    subprocess.run(["lake", "build", "Glamsterdam.Gloas7732.BuilderRequests", "Glamsterdam.Gloas7732.PayloadAttestation"], cwd=ROOT, check=True)
    blst = Path(os.environ.get("GLOAS_BLST_DIR", ROOT / ".blst")).resolve()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=blst, text=True).strip()
    if revision != "e7f90de551e8df682f3cc99067d204d8b90d27ad":
        raise ValueError(f"unexpected blst revision {revision}")
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
                    HERE / "bridge.c", HERE / "ssz_bridge.c", HERE / "bls_bridge.c", f"-I{blst / 'bindings'}", ssz_c, generated, ir / "Common/Prelude.c", ir / "Common/MetaSpec.c",
                    ir / "Gloas7732/Spec.c", ir / "Gloas7732/BuilderRequests.c", ir / "Gloas7732/PayloadAttestation.c", f"-L{runtime}", blst / "libblst.a", "-lleanshared",
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
    lib.verify_builder_signature.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.c_char_p, ctypes.c_size_t]
    lib.verify_builder_signature.restype = ctypes.c_int
    lib.verify_ptc_signature.argtypes = [ctypes.c_char_p, ctypes.c_size_t] * 5
    lib.verify_ptc_signature.restype = ctypes.c_int
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
            if name not in cases or not member.isfile():
                continue
            if not path[-1].endswith(".ssz_snappy") and path[-1] not in {"config.yaml", "meta.yaml"}:
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


def check_ptc(lib, spec, case, decoded, pre, data, config, meta):
    att = decoded("payload_attestation", spec.PayloadAttestation)
    as_int = lambda value: int.from_bytes(bytes(value), "big")
    data.update(attestedSlot=int(att.data.slot), attestedRoot=as_int(att.data.beacon_block_root),
                parentRoot=as_int(pre.latest_block_header.parent_root),
                gloasEpoch=int(config.get("GLOAS_FORK_EPOCH", spec.config.GLOAS_FORK_EPOCH)),
                window=[[int(i) for i in committee] for committee in pre.ptc_window],
                bits=[bool(b) for b in att.aggregation_bits], pubkeys=[as_int(v.pubkey) for v in pre.validators],
                currentVersion=as_int(pre.fork.current_version), previousVersion=as_int(pre.fork.previous_version),
                forkEpoch=int(pre.fork.epoch), verifiedSignature=None)
    actual = replay(lib, data)
    if "signers" in actual:
        args = [b"".join(key.to_bytes(48, "big") for key in actual["signers"]),
                att.data.encode_bytes(), bytes(att.signature),
                actual["version"].to_bytes(4, "big"), bytes(pre.genesis_validators_root)]
        enabled = meta.get("bls_setting", 0) != 2
        valid = lib.verify_ptc_signature(*(v for arg in args for v in (arg, len(arg)))) if enabled else 1
        if valid not in (0, 1):
            raise ValueError("malformed PTC BLS adapter input")
        data["verifiedSignature"] = bool(valid)
        actual = replay(lib, data)
    accepted = actual["accepted"]
    if accepted != ("post.ssz_snappy" in case):
        raise ValueError(f"unexpected PTC acceptance: {accepted}")
    if accepted and pre.encode_bytes() != snappy.decompress(case["post.ssz_snappy"]):
        raise ValueError("read-only PTC operation disagrees with the official post-state")
    return {"status": "full_pass", "outcome": "accepted" if accepted else "rejected",
            "evidence": "lean_complete_post_state" if accepted else "lean_rejection"}


def check_parent(lib, spec, case, decoded, state, data):
    block = decoded("block", spec.BeaconBlock)
    bid = state.latest_execution_payload_bid
    requests = block.body.parent_execution_requests
    limits = [(len(getattr(requests, field)), int(getattr(spec, limit))) for field, limit in (
        ("withdrawals", "MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD"),
        ("consolidations", "MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD"),
        ("builder_deposits", "MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD"),
        ("builder_exits", "MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD"))]
    parent_slot = int(state.latest_block_header.slot)
    data.update(parentHash=int.from_bytes(bytes(bid.block_hash), "big"),
                bidParentHash=int.from_bytes(bytes(block.body.signed_execution_payload_bid.message.parent_block_hash), "big"),
                emptyRequests=requests == spec.ExecutionRequests.empty(),
                requestsRoot=bytes(spec.hash_tree_root(requests)).hex(),
                requestsCommitment=bytes(bid.execution_requests_root).hex(), requestLimits=limits,
                parentSlot=parent_slot, parentBid={"feeRecipient": int.from_bytes(bytes(bid.fee_recipient), "big"),
                "amount": int(bid.value), "builderIndex": int(bid.builder_index)})
    actual = replay(lib, data)
    path = actual["path"]
    rejected = path.startswith("reject_")
    if rejected != ("post.ssz_snappy" not in case):
        raise ValueError(f"parent result disagrees with fixture on path {path}")
    if rejected:
        return {"status": "full_pass", "evidence": "lean_rejection", "path": path}
    queued = 0 if path == "empty_parent" else len(actual["withdrawals"]) - len(data["withdrawals"])
    if path != "empty_parent":
        apply_output(spec, state, "builder_pending_payments", actual)
        # Nested request processing is outside the parent settlement theorem.
        for operations, process in (
            (requests.deposits, spec.process_deposit_request),
            (requests.withdrawals, spec.process_withdrawal_request),
            (requests.consolidations, spec.process_consolidation_request),
            (requests.builder_deposits, spec.process_builder_deposit_request),
            (requests.builder_exits, spec.process_builder_exit_request),
        ):
            for operation in operations:
                process(state, operation)
        state.execution_payload_availability[parent_slot % spec.SLOTS_PER_HISTORICAL_ROOT] = True
        state.latest_block_hash = bid.block_hash
    expected = decoded("post", spec.BeaconState)
    if state.encode_bytes() != expected.encode_bytes():
        field = next(f for f in spec.BeaconState.model_fields if getattr(state, f) != getattr(expected, f))
        raise ValueError(f"{path}: first differing BeaconState field: {field}")
    return {"status": "hybrid_pass", "evidence": "hybrid_complete_post_state", "path": path,
            "withdrawals_appended": queued,
            "lean_fields": [] if path == "empty_parent" else ["builder_pending_payments", "builder_pending_withdrawals"]}


def check_bid(lib, spec, case, decoded, state, data, meta):
    signed = decoded("execution_payload_bid", spec.SignedExecutionPayloadBid)
    bid = signed.message
    index = int(bid.builder_index)
    data["bid"] = {"feeRecipient": int.from_bytes(bytes(bid.fee_recipient), "big"),
                   "amount": int(bid.value), "builderIndex": index}
    covered = None
    if index == spec.BUILDER_INDEX_SELF_BUILD:
        valid = bid.value == 0 and signed.signature == spec.bls.G2_POINT_AT_INFINITY
    else:
        valid = (index < len(state.builders) and spec.is_active_builder(state, index)
                 and state.builders[index].version == spec.PAYLOAD_BUILDER_VERSION)
        if valid:
            covered = replay(lib, dict(data, phase="coverage", balance=int(state.builders[index].balance)))["covered"]
            valid = covered and (meta.get("bls_setting") == 2 or spec.verify_execution_payload_bid_signature(state, signed))
    valid = (valid and len(bid.blob_kzg_commitments) <= spec.get_blob_parameters(spec.get_current_epoch(state)).max_blobs_per_block
             and bid.slot == state.slot and state.slot > spec.GENESIS_SLOT
             and bid.parent_block_hash == state.latest_block_hash and bid.block_hash != bid.parent_block_hash
             and bid.parent_block_root == spec.get_block_root_at_slot(state, state.slot - 1)
             and bid.prev_randao == spec.get_randao_mix(state, spec.get_current_epoch(state)))
    if bool(valid) != ("post.ssz_snappy" in case):
        raise ValueError(f"unexpected bid acceptance {valid}; builder coverage {covered}")
    if not valid:
        return {"status": "full_pass" if covered is False else "python_rejection",
                "evidence": "lean_rejection" if covered is False else "python_rejection",
                "lean_coverage_guard": covered}
    output = replay(lib, dict(data, phase="record", proposer=int(spec.get_beacon_proposer_index(state))))
    apply_output(spec, state, "builder_pending_payments", output)
    state.latest_execution_payload_bid = bid
    expected = decoded("post", spec.BeaconState)
    if state.encode_bytes() != expected.encode_bytes():
        field = next(f for f in spec.BeaconState.model_fields if getattr(state, f) != getattr(expected, f))
        raise ValueError(f"accepted bid: first differing field {field}")
    return {"status": "hybrid_pass", "evidence": "hybrid_complete_post_state",
            "lean_coverage_guard": covered, "positive_payment_recorded": bool(bid.value)}


def check_attestation(lib, spec, case, decoded, state, data, meta):
    att = decoded("attestation", spec.Attestation)
    vote = att.data
    epoch = spec.get_current_epoch(state)
    delay = int(state.slot) - int(vote.slot)
    def reject(reason, lean=False, after_lean=False):
        if "post.ssz_snappy" in case:
            raise ValueError(f"unexpected attestation rejection at {reason}")
        return {"status": "full_pass" if lean else "python_rejection",
                "evidence": "lean_rejection" if lean else "python_rejection", "reason": reason,
                "lean_flag_validation_ran": lean or after_lean}
    if (vote.target.epoch not in (spec.get_previous_epoch(state), epoch)
            or vote.target.epoch != spec.compute_epoch_at_slot(vote.slot)
            or delay < spec.MIN_ATTESTATION_INCLUSION_DELAY or vote.index >= 2):
        return reject("epoch, inclusion delay or payload index")
    offset = 0
    for ci in spec.get_committee_indices(att.committee_bits):
        if ci >= spec.get_committee_count_per_slot(state, vote.target.epoch):
            return reject("committee index")
        committee = spec.get_beacon_committee(state, vote.slot, ci)
        bits = list(att.aggregation_bits)[offset:offset + len(committee)]
        if not any(bits):
            return reject("empty committee participation")
        offset += len(committee)
    if len(att.aggregation_bits) != offset:
        return reject("committee bit count")
    current = vote.target.epoch == epoch
    participation = state.current_epoch_participation if current else state.previous_epoch_participation
    justified = state.current_justified_checkpoint if current else state.previous_justified_checkpoint
    indices = sorted(spec.get_attesting_indices(state, att))
    data.update(voteSlot=int(vote.slot), targetEpoch=int(vote.target.epoch), head=bytes(vote.beacon_block_root).hex(),
                slotRoot=bytes(spec.get_block_root_at_slot(state, vote.slot)).hex(),
                prevRoot=bytes(spec.get_block_root_at_slot(state, vote.slot - 1)).hex() if vote.slot else "",
                payloadIndex=int(vote.index), source=vote.source.encode_bytes().hex(),
                justified=justified.encode_bytes().hex(), target=bytes(vote.target.root).hex(),
                targetRoot=bytes(spec.get_block_root(state, vote.target.epoch)).hex(),
                minDelay=int(spec.MIN_ATTESTATION_INCLUSION_DELAY),
                available=bool(state.execution_payload_availability[meta["parent_slot"] % spec.SLOTS_PER_HISTORICAL_ROOT]),
                attesters=[dict(index=int(v), flags=int(participation[v]), balance=int(state.validators[v].effective_balance))
                           for v in indices])
    result = replay(lib, data)
    if not result["accepted"]:
        return reject("source or same-slot payload index", lean=True)
    indexed = spec.get_indexed_attestation(state, att)
    if not indexed.attesting_indices or (meta.get("bls_setting") != 2 and not spec.is_valid_indexed_attestation(state, indexed)):
        return reject("indexed attestation or signature", after_lean=True)
    if "post.ssz_snappy" not in case:
        raise ValueError("unexpected attestation acceptance")
    participation = state.current_epoch_participation if result["current"] else state.previous_epoch_participation
    numerator = 0
    for index, flags in result["flags"]:
        new_bits = int(participation[index]) ^ flags
        for flag, weight in enumerate(spec.PARTICIPATION_FLAG_WEIGHTS):
            if new_bits & (1 << flag):
                numerator += int(spec.get_base_reward(state, index)) * int(weight)
        participation[index] = flags
    payment = state.builder_pending_payments[result["index"]]
    delta = result["weight"] - int(payment.weight)
    payment.weight = result["weight"]
    denominator = (spec.WEIGHT_DENOMINATOR - spec.PROPOSER_WEIGHT) * spec.WEIGHT_DENOMINATOR // spec.PROPOSER_WEIGHT
    spec.increase_balance(state, spec.get_beacon_proposer_index(state), spec.Gwei(numerator // denominator))
    expected = decoded("post", spec.BeaconState)
    if state.encode_bytes() != expected.encode_bytes():
        field = next(f for f in spec.BeaconState.model_fields if getattr(state, f) != getattr(expected, f))
        raise ValueError(f"attestation: first differing field {field}")
    return {"status": "hybrid_pass", "evidence": "hybrid_complete_post_state",
            "credited_weight": delta, "participants": len(indices), "payment_index": result["index"]}


def check_case(lib, spec, name, case):
    handler = name.split("/")[3]
    def decoded(field, typ):
        return typ.decode_bytes(snappy.decompress(case[field + ".ssz_snappy"]))
    pre = decoded("pre", spec.BeaconState)
    data = queues(pre)
    data.update(handler=handler, slot=int(pre.slot), slotsPerEpoch=int(spec.SLOTS_PER_EPOCH))
    yaml = YAML(typ="safe")
    config = yaml.load(case.get("config.yaml", b"{}"))
    meta = yaml.load(case.get("meta.yaml", b"{}"))
    if handler == "attestation":
        return check_attestation(lib, spec, case, decoded, pre, data, meta)
    if handler == "execution_payload_bid":
        return check_bid(lib, spec, case, decoded, pre, data, meta)
    if handler == "parent_execution_payload":
        return check_parent(lib, spec, case, decoded, pre, data)
    if handler == "payload_attestation":
        return check_ptc(lib, spec, case, decoded, pre, data, config, meta)
    if handler == "builder_pending_payments":
        data.update(increment=int(spec.EFFECTIVE_BALANCE_INCREMENT), validators=[
            dict(activationEpoch=int(v.activation_epoch), exitEpoch=int(v.exit_epoch),
                 effectiveBalance=int(v.effective_balance)) for v in pre.validators])
    else:
        data.update(builders=[builder(b) for b in pre.builders],
                    delay=int(config.get("MIN_BUILDER_WITHDRAWABILITY_DELAY", spec.config.MIN_BUILDER_WITHDRAWABILITY_DELAY)))
        if handler == "builder_exit_request":
            request = decoded(handler, spec.BuilderExitRequest)
            data.update(source=int.from_bytes(bytes(request.source_address), "big"),
                        finalized=int(pre.finalized_checkpoint.epoch))
        else:
            request = decoded(handler, spec.BuilderDepositRequest)
            data.update(prefix=request.withdrawal_credentials[0], amount=int(request.amount),
                        credentials=int.from_bytes(bytes(request.withdrawal_credentials), "big"),
                        verifiedSignature=None)
        data["pubkey"] = int.from_bytes(bytes(request.pubkey), "big")
    control = None
    actual = replay(lib, data)
    if actual.get("verifyBuilderSignature"):
        raw = snappy.decompress(case[handler + ".ssz_snappy"])
        version = bytes(spec.config.GENESIS_FORK_VERSION)
        valid = lib.verify_builder_signature(raw, len(raw), version, len(version))
        if valid not in (0, 1):
            raise ValueError("invalid builder signature adapter input")
        if name.endswith("/process_builder_deposit_request__new_builder"):
            alternate = bytes([version[0] ^ 1]) + version[1:]
            if valid != 1 or lib.verify_builder_signature(raw, len(raw), alternate, len(alternate)) != 0:
                raise AssertionError("builder signing domain control failed")
            control = "signature rejected with altered genesis fork version"
        data["verifiedSignature"] = bool(valid)
        actual = replay(lib, data)
    if "unsupported" in actual:
        return {"status": "unsupported", "dependency": actual["unsupported"]}
    expected = decoded("post", spec.BeaconState)
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
    return {"status": "full_pass", "evidence": "lean_complete_post_state",
            **({"negative_control": control} if control else {})}


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


HANDLER_DEPENDENCIES = {
    ("operations", "attestation"): "committee shuffling, indexed aggregate signature checks, participation flags and proposer rewards",
    ("operations", "parent_execution_payload"): "payload binding, parent execution requests, and composed availability/payment updates",
    ("operations", "withdrawals"): "validator and builder sweeps, queue limits and withdrawal-index transitions",
    ("operations", "payload_attestation"): "payload-timeliness committee derivation and aggregate signature verification",
    ("operations", "proposer_slashing"): "signed conflicting headers and the complete validator slashing transition",
    ("operations", "attester_slashing"): "indexed attestation signatures, slashability and validator balance updates",
    ("operations", "sync_aggregate"): "sync committee aggregate signature, participation rewards and penalties",
    ("operations", "execution_payload_bid"): "bid validity, builder signatures, consensus binding and pending-payment insertion",
    ("epoch_processing", "pending_deposits"): "pending deposit queue, churn budget and validator activation accounting",
    ("epoch_processing", "registry_updates"): "validator eligibility, ejection and churn-limited activation",
}


def fingerprint(ids):
    return hashlib.sha256(("\n".join(sorted(ids)) + "\n").encode()).hexdigest()


def check_claim_paths(results, supplemental):
    """Keep strong evidence from turning into a no-op with unchanged pass counts."""
    att = [row for key, row in results.items() if "/operations/attestation/" in key]
    bid = [row for key, row in results.items() if "/operations/execution_payload_bid/" in key]
    parent = [row for key, row in results.items() if "/operations/parent_execution_payload/" in key]
    evidence = {
        "fork_cases_with_existing_builder_topups": sum(r.get("existing_builder_topups", 0) > 0 for r in results.values()),
        "withdrawal_cases_with_builder_debits": sum(r.get("builder_debits", 0) > 0 for r in results.values()),
        "slashing_cases_clearing_payment_entries": sum(r.get("changed_entries", 0) > 0 for r in results.values()),
        "ordinary_attestations": len(att),
        "positive_weight_changes": sum(row.get("credited_weight", 0) > 0 for row in att),
        "coverage_guard_accepted": sum(row.get("lean_coverage_guard") is True for row in bid),
        "coverage_guard_rejected": sum(row.get("lean_coverage_guard") is False for row in bid),
        "positive_bid_entries": sum(row.get("positive_payment_recorded", False) for row in bid),
        "parent_paths": dict(Counter(row.get("path") for row in parent)),
        "supplemental_sequences_and_controls": sum(map(len, supplemental.values())),
    }
    expected = {"fork_cases_with_existing_builder_topups": 6, "withdrawal_cases_with_builder_debits": 42,
                "slashing_cases_clearing_payment_entries": 6, "ordinary_attestations": 127, "positive_weight_changes": 6,
                "coverage_guard_accepted": 8, "coverage_guard_rejected": 6, "positive_bid_entries": 6,
                "parent_paths": {"current_epoch": 26, "previous_epoch": 2, "older_parent": 6, "empty_parent": 4,
                                 "reject_empty_requests": 2, "reject_limit": 8},
                "supplemental_sequences_and_controls": 8}
    if evidence != expected:
        raise ValueError(f"claim path evidence changed: {evidence}")
    return evidence


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
    report["claim_source_review"] = source_manifest(importlib.import_module("eth_consensus_specs.gloas.minimal"))
    results = report["cases"]
    with tempfile.TemporaryDirectory() as tmp:
        sources, report["gloas_python_only"] = collect_sources(Path(tmp))
        lib = compile_bridge(Path(tmp))
        report["ssz_controls"] = check_codec_controls(lib)
        report["supplemental_checks"] = {}
        report["generated_payment_histories"] = {}
        for preset in ("minimal", "mainnet"):
            spec = importlib.import_module(f"eth_consensus_specs.gloas.{preset}")
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                               cwd=Path(spec.__file__).parent, text=True).strip()
            if revision != SPEC:
                raise ValueError(f"{preset}: unexpected PySpec revision {revision}")
            selected = []
            static = set()
            screened = set()
            for name, scope in cases.items():
                config, _, runner, handler, _, _ = name.split("/")
                if config != preset:
                    continue
                if scope == "compliance":
                    results[name] = {"status": "separate_compliance", "evidence": "outside_scope"}
                elif runner == "ssz_static":
                    static.add(name)
                elif (runner, handler) in {("fork", "fork"), ("operations", "withdrawals"), ("operations", "proposer_slashing")}:
                    screened.add(name)
                elif (runner, handler) == ("sanity", "blocks") or runner in {"transition", "random", "finality"}:
                    screened.add(name)
                elif f"{runner}/{handler}" in HANDLERS:
                    selected.append(name)
                else:
                    results[name] = {"status": "unsupported", "evidence": "outside_scope", "dependency": HANDLER_DEPENDENCIES.get((runner, handler), DEPENDENCIES[runner])}
            check_archive(lib, spec, args.archives / f"{preset}.tar.gz", static, results)
            for name, case in screen_cases(args.archives / f"{preset}.tar.gz", screened):
                if name in results:
                    raise ValueError(f"duplicate screened case {name}")
                runner = name.split("/")[2]
                if runner in {"operations", "fork"}:
                    results[name] = screen_state(lib, spec, name, case, replay, queues)
                else:
                    row = screen_blocks(spec, runner, case)
                    ops = row["gloas_operations_in_valid_blocks"]
                    if row["official_acceptance"] and ops.get("nonzero_bids", 0) and ops["execution_payload_bid"] >= 2:
                        if runner == "transition":
                            raise ValueError("new cross-fork paid history needs a pre-fork decoder")
                        row = replay_history(lib, spec, case, sys.modules[__name__])
                        if name.endswith("/builder_payment_after_missed_epochs"):
                            report["generated_payment_histories"][preset] = equal_amount_history(
                                lib, spec, case["pre.ssz_snappy"], sys.modules[__name__])
                    results[name] = row
            for name, case in read_cases(args.archives / f"{preset}.tar.gz", selected).items():
                try:
                    results[name] = check_case(lib, spec, name, case)
                    controls = additional_checks(lib, spec, name, case, replay, queues, apply_output, check_case, check_parent)
                    if controls:
                        report["supplemental_checks"][name] = controls
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
    by_handler = defaultdict(Counter)
    for name, row in results.items():
        by_handler["/".join(name.split("/")[:4])][row["status"]] += 1
    report["by_preset_runner_handler"] = dict(by_handler)
    report["claim_paths"] = check_claim_paths(results, report["supplemental_checks"])
    print(report["counts"])
    args.report.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    baselines = {status: fingerprint(k for k, r in results.items() if r["status"] == status)
                 for status in report["counts"]}
    if "failed" in baselines or baselines != json.loads((HERE / "coverage-baseline.json").read_text()):
        raise SystemExit("coverage differs from reviewed baseline; inspect per-case report")


if __name__ == "__main__":
    main()
