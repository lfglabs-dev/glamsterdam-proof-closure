"""Screen surrounding official fixtures without counting whole-block conformance."""
from collections import Counter
from itertools import groupby
import tarfile

import snappy
from ruamel.yaml import YAML


def screen_cases(path, selected):
    # Stream one fixture at a time. Archive inventory independently checks case IDs.
    with tarfile.open(path, "r|gz") as archive:
        for name, members in groupby(archive, lambda member: member.name.removeprefix("tests/").rsplit("/", 1)[0]):
            if name not in selected:
                continue
            files = {m.name.rsplit("/", 1)[-1]: archive.extractfile(m).read() for m in members
                     if m.isfile() and (m.name.endswith(".ssz_snappy") or m.name.endswith("meta.yaml"))}
            if files:
                yield name, files


def screen_blocks(spec, runner, files):
    meta = YAML(typ="safe").load(files["meta.yaml"])
    last_pre_fork = meta.get("fork_block", -1) if runner == "transition" else -1
    operations = Counter()
    complete = "post.ssz_snappy" in files
    # For negative sequences the format establishes that the last block fails.
    # Its body alone cannot establish which operations ran before rejection.
    final_candidates = Counter()
    for i in range(meta["blocks_count"]):
        if i <= last_pre_fork:
            continue
        signed = spec.SignedBeaconBlock.decode_bytes(snappy.decompress(files[f"blocks_{i}.ssz_snappy"]))
        body = signed.message.body
        reached = operations if complete or i + 1 < meta["blocks_count"] else final_candidates
        reached["parent_execution_payload"] += 1
        reached["execution_payload_bid"] += 1
        reached["ordinary_attestations"] += len(body.attestations)
        reached["proposer_slashings"] += len(body.proposer_slashings)
        reached["builder_exit_requests_in_parent"] += len(body.parent_execution_requests.builder_exits)
        reached["builder_deposit_requests_in_parent"] += len(body.parent_execution_requests.builder_deposits)
    return {"status": "unsupported", "evidence": "screened_block_inputs", "official_acceptance": complete,
            "gloas_operations_in_valid_blocks": dict(operations),
            "operations_in_final_rejected_block": dict(final_candidates),
            "dependency": "Whole-chain slot, epoch and block execution. No intermediate state was supplied to Lean."}

def check_onboarding(lib, spec, pre, expected, replay):
    validators = {bytes(v.pubkey) for v in pre.validators}
    balances = {}
    pending = []
    existing_builder_topups = 0
    for deposit in pre.pending_deposits:
        key = bytes(deposit.pubkey)
        registered = key in balances
        if key in validators or (not registered and spec.is_pending_validator(pending, deposit.pubkey)):
            pending.append(deposit)
            continue
        prefix = bytes(deposit.withdrawal_credentials)[0]
        valid = (not registered and prefix == spec.BUILDER_WITHDRAWAL_PREFIX[0]
                 and spec.is_valid_deposit_signature(deposit.pubkey, deposit.withdrawal_credentials,
                                                      deposit.amount, deposit.signature))
        consume, amount = replay(lib, dict(handler="onboard", registered=registered, prefix=prefix,
                                           valid=bool(valid), balance=balances.get(key, 0), amount=int(deposit.amount)))
        if not consume:
            pending.append(deposit)
        elif registered or valid:
            balances[key] = amount
            existing_builder_topups += int(registered)
    if list(balances.items()) != [(bytes(b.pubkey), int(b.balance)) for b in expected.builders]:
        raise ValueError("fork onboarding: first mismatch in builder keys or balances")
    if [p.encode_bytes() for p in pending] != [p.encode_bytes() for p in expected.pending_deposits]:
        raise ValueError("fork onboarding: first mismatch in remaining deposits")
    return existing_builder_topups


def screen_state(lib, spec, name, files, replay, queues):
    handler = name.split("/")[3]
    def decode(key, typ):
        return typ.decode_bytes(snappy.decompress(files[key + ".ssz_snappy"]))
    if "post.ssz_snappy" not in files:
        return {"status": "unsupported", "evidence": "outside_scope",
                "dependency": "Negative case requires full upstream validation before this projected operation."}
    expected = decode("post", spec.BeaconState)
    if handler == "fork":
        pre = decode("pre", spec.fulu.BeaconState)
        bit = replay(lib, {"handler": handler, "size": int(spec.SLOTS_PER_HISTORICAL_ROOT), "slot": int(pre.slot)})
        if bit is not bool(expected.execution_payload_availability[pre.slot % spec.SLOTS_PER_HISTORICAL_ROOT]):
            raise ValueError("fork slot availability bit")
        topups = check_onboarding(lib, spec, pre, expected, replay)
        return {"status": "partial_pass", "evidence": "lean_fields",
                "lean_fields": ["fork slot availability bit", "builder balances after deposit routing"],
                "existing_builder_topups": topups,
                "pending_deposits_at_fork": len(pre.pending_deposits),
                "dependency": "Python supplies validator membership, pending-validator lookup and signatures; other upgrade fields are outside the projection"}
    pre = decode("pre", spec.BeaconState)
    if handler == "withdrawals":
        full = pre.latest_block_hash == pre.latest_execution_payload_bid.block_hash
        planned = spec.get_expected_withdrawals(pre).withdrawals if full else []
        debits = [(int(spec.convert_validator_index_to_builder_index(w.validator_index)), int(w.amount))
                  for w in planned if spec.is_builder_index(w.validator_index)]
        after = replay(lib, {"handler": handler, "balances": [int(b.balance) for b in pre.builders], "debits": debits})
        if after != [int(b.balance) for b in expected.builders]:
            raise ValueError("withdrawal debit differs from expected builder balances")
        return {"status": "partial_pass", "evidence": "lean_fields", "lean_fields": ["builders[].balance"],
                "builder_debits": len(debits), "total_debited": sum(v for _, v in debits),
                "dependency": "Withdrawal selection and cap are supplied by Python"}
    slashing = decode("proposer_slashing", spec.ProposerSlashing)
    proposer = int(slashing.signed_header_1.message.proposer_index)
    before = queues(pre)
    result = replay(lib, dict(before, handler=handler, proposer=proposer,
                              slotsPerEpoch=int(spec.SLOTS_PER_EPOCH), slot=int(pre.slot)))
    if result != queues(expected)["payments"]:
        raise ValueError("slashing differs on builder_pending_payments")
    return {"status": "partial_pass", "evidence": "lean_fields", "lean_fields": ["builder_pending_payments"],
            "changed_entries": sum(a != b for a, b in zip(before["payments"], result, strict=True)),
            "dependency": "Slashing validity, validator penalties and rewards are outside this projection"}
