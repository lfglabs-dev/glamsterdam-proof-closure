"""Replay selected valid block sequences with pinned Python and the compiled payment rules."""
from contextlib import ExitStack
from unittest.mock import patch

import snappy
from ruamel.yaml import YAML

def fixture_config(spec, raw):
    if raw is None:
        return spec.config
    recorded = YAML(typ="safe").load(raw)
    changes = {}
    for key, value in spec.config._asdict().items():
        comparable = int.from_bytes(value, "big") if isinstance(value, bytes) else value
        if isinstance(value, tuple):
            comparable = list(value)
        if comparable != recorded[key]:
            if not key.endswith("_FORK_EPOCH"):
                raise ValueError(f"unexpected config override in selected history: {key}")
            changes[key] = spec.Epoch(recorded[key])
    return spec.config._replace(**changes)


def replay_history(lib, spec, files, adapter, identity_controls=False):
    meta = YAML(typ="safe").load(files["meta.yaml"])
    state = spec.BeaconState.decode_bytes(snappy.decompress(files["pre.ssz_snappy"]))
    reference = state.model_copy(deep=True)
    events = []
    controls = []

    def inputs(st, handler):
        return dict(adapter.queues(st), handler=handler, slot=int(st.slot), slotsPerEpoch=int(spec.SLOTS_PER_EPOCH))

    def operation(handler, function, check):
        def apply(st, op, *extra):
            prior = st.model_copy(deep=True) if identity_controls and handler == "parent_execution_payload" else None
            expected = st.model_copy(deep=True)
            function(expected, op, *extra)
            def decoded(key, typ):
                return expected if key == "post" else op
            args = (lib, spec, {"post.ssz_snappy": True}, decoded, st, inputs(st, handler))
            if handler == "attestation":
                outcome = check(*args, dict(meta, parent_slot=int(extra[0])))
            elif handler == "execution_payload_bid":
                outcome = check(*args, meta)
            else:
                outcome = check(*args)
            if identity_controls and handler == "parent_execution_payload" and outcome["withdrawals_appended"]:
                # Mutate Lean's output at the ABI boundary while retaining its amount.
                for field in ("feeRecipient", "builderIndex"):
                    alternative = next(e["bid"] for e in events if e["operation"] == "execution_payload_bid"
                                       and e["bid"]["amount"] == expected.builder_pending_withdrawals[-1].amount
                                       and e["bid"]["builder"] != expected.builder_pending_withdrawals[-1].builder_index)
                    value = int(alternative["recipient"], 16) if field == "feeRecipient" else alternative["builder"]
                    original = adapter.replay
                    def mutate(lib, data):
                        output = original(lib, data)
                        output["withdrawals"][-1][field] = value
                        return output
                    with patch.object(adapter, "replay", mutate):
                        try:
                            check(lib, spec, {"post.ssz_snappy": True}, decoded, prior.model_copy(deep=True),
                                  inputs(prior, handler))
                        except ValueError as error:
                            if "first differing BeaconState field: builder_pending_withdrawals" not in str(error):
                                raise
                        else:
                            raise ValueError(f"equal-amount {field} swap escaped comparison")
                    controls.append(field)
            event = dict(operation=handler, slot=int(st.slot), **outcome)
            if handler == "execution_payload_bid":
                event["bid"] = dict(amount=int(op.message.value), builder=int(op.message.builder_index),
                                    recipient=bytes(op.message.fee_recipient).hex())
            if handler == "parent_execution_payload" and outcome["withdrawals_appended"]:
                event["settled"] = adapter.withdrawal(st.builder_pending_withdrawals[-1])
            events.append(event)
        return apply

    def rotate(st):
        expected = st.model_copy(deep=True)
        epoch_rule(expected)
        data = inputs(st, "builder_pending_payments")
        data.update(increment=int(spec.EFFECTIVE_BALANCE_INCREMENT), validators=[
            dict(activationEpoch=int(v.activation_epoch), exitEpoch=int(v.exit_epoch), effectiveBalance=int(v.effective_balance))
            for v in st.validators])
        before = len(st.builder_pending_withdrawals)
        adapter.apply_output(spec, st, "builder_pending_payments", adapter.replay(lib, data))
        if st.encode_bytes() != expected.encode_bytes():
            raise ValueError("payment history diverged at epoch rotation")
        events.append(dict(operation="epoch_quorum", slot=int(st.slot),
                           settled=[adapter.withdrawal(w) for w in list(st.builder_pending_withdrawals)[before:]]))

    def debit(st, withdrawals):
        expected = st.model_copy(deep=True)
        debit_rule(expected, withdrawals)
        debits = []
        for w in withdrawals:
            if spec.is_builder_index(w.validator_index):
                index = int(spec.convert_validator_index_to_builder_index(w.validator_index))
                debits.append([index, int(w.amount)])
                events.append(dict(operation="debit", slot=int(st.slot), builder=index,
                                   amount=int(w.amount), recipient=bytes(w.address).hex()))
            else:
                spec.decrease_balance(st, w.validator_index, w.amount)
        balances = adapter.replay(lib, dict(handler="withdrawals", balances=[int(b.balance) for b in st.builders], debits=debits))
        for index, _ in debits:
            st.builders[index].balance = balances[index]
        if st.encode_bytes() != expected.encode_bytes():
            raise ValueError("payment history diverged at withdrawal application")

    epoch_rule = spec.process_builder_pending_payments
    debit_rule = spec.apply_withdrawals
    hooks = {"process_builder_pending_payments": rotate, "apply_withdrawals": debit}
    for handler, check in (("attestation", adapter.check_attestation), ("execution_payload_bid", adapter.check_bid),
                           ("parent_execution_payload", adapter.check_parent)):
        fn = "process_" + handler
        hooks[fn] = operation(handler, getattr(spec, fn), check)
    with patch.object(spec, "config", fixture_config(spec, files.get("config.yaml"))), patch.object(spec.bls, "bls_active", meta.get("bls_setting") != 2):
        for i in range(meta["blocks_count"]):
            block = spec.SignedBeaconBlock.decode_bytes(snappy.decompress(files[f"blocks_{i}.ssz_snappy"]))
            spec.state_transition(reference, block)
            with ExitStack() as stack:
                for fn, impl in hooks.items():
                    stack.enter_context(patch.object(spec, fn, impl))
                spec.state_transition(state, block)
            if state.encode_bytes() != reference.encode_bytes():
                raise ValueError(f"payment history diverged after signed block {i}")
    if state.encode_bytes() != snappy.decompress(files["post.ssz_snappy"]):
        raise ValueError("complete payment history diverged from official post-state")
    return dict(status="hybrid_pass", evidence="hybrid_complete_block_history", blocks=meta["blocks_count"], events=events, identity_controls=controls)


def equal_amount_history(lib, spec, official_pre, adapter):
    """Generate three signed blocks. First bid earns quorum; second has a late full child."""
    from eth_consensus_specs.test.helpers.attestations import get_valid_attestations_at_slot
    from eth_consensus_specs.test.helpers.block import build_empty_block
    from eth_consensus_specs.test.helpers.keys import builder_privkeys
    from eth_consensus_specs.test.helpers.state import state_transition_and_sign_block

    state = spec.BeaconState.decode_bytes(snappy.decompress(official_pre))
    files = {"pre.ssz_snappy": official_pre, "meta.yaml": b"{blocks_count: 3, bls_setting: 1}"}
    amount = 1_000_000
    for index in (0, 1):
        block = build_empty_block(spec, state, slot=state.slot + 1)
        bid = block.body.signed_execution_payload_bid.message
        bid.block_hash = spec.Hash32(bytes([0x41 + index]) * 32)
        bid.builder_index = index
        bid.fee_recipient = bytes([0xA1 + index]) * 20
        bid.value = amount
        block.body.signed_execution_payload_bid.signature = spec.get_execution_payload_bid_signature(
            state, bid, builder_privkeys[index])
        if index == 1:
            vote_state = state.model_copy(deep=True)
            spec.process_slots(vote_state, block.slot)
            votes = get_valid_attestations_at_slot(vote_state, spec, state.slot, payload_index=0)
            block.body.attestations = type(block.body.attestations)(data=votes)
        signed = state_transition_and_sign_block(spec, state, block)
        files[f"blocks_{index}.ssz_snappy"] = snappy.compress(signed.encode_bytes())
    slot = spec.compute_start_slot_at_epoch(spec.get_current_epoch(state) + 2) + 1
    block = build_empty_block(spec, state, slot=slot)
    block.body.signed_execution_payload_bid.message.parent_block_hash = state.latest_execution_payload_bid.block_hash
    signed = state_transition_and_sign_block(spec, state, block)
    files["blocks_2.ssz_snappy"] = snappy.compress(signed.encode_bytes())
    files["post.ssz_snappy"] = snappy.compress(state.encode_bytes())
    result = replay_history(lib, spec, files, adapter, identity_controls=True)
    events = result["events"]
    ids = [(e["builder"], e["recipient"], e["amount"]) for e in events if e["operation"] == "debit"]
    expected = [(i, (bytes([0xA1 + i]) * 20).hex(), amount) for i in (0, 1)]
    if ids != expected or result["identity_controls"] != ["feeRecipient", "builderIndex"]:
        raise ValueError(f"unexpected equal-amount payment history: {ids}")
    if not any(e["operation"] == "epoch_quorum" and e["settled"] for e in events):
        raise ValueError("generated history did not settle the first bid through quorum")
    return result
