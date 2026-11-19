"""Additional differential and mutation checks, outside the official denominator."""
from unittest.mock import patch

import snappy


def additional_checks(lib, spec, name, files, replay, queues, apply_output, check_case, check_parent):
    controls = []
    tag = name.rsplit("/", 1)[-1]
    if tag == "builder_payment_weight_tracking":
        pre = spec.BeaconState.decode_bytes(snappy.decompress(files["pre.ssz_snappy"]))
        att = spec.Attestation.decode_bytes(snappy.decompress(files["attestation.ssz_snappy"]))
        from ruamel.yaml import YAML
        parent_slot = YAML(typ="safe").load(files["meta.yaml"])["parent_slot"]
        spec.process_attestation(pre, att, parent_slot)
        if pre.encode_bytes() != snappy.decompress(files["post.ssz_snappy"]):
            raise ValueError("reference first vote differs from official post-state")
        second_pre = pre.encode_bytes()
        spec.process_attestation(pre, att, parent_slot)
        second_expected = pre.encode_bytes()
        repeat = dict(files, **{"pre.ssz_snappy": snappy.compress(second_pre),
                               "post.ssz_snappy": snappy.compress(second_expected)})
        outcome = check_case(lib, spec, name, repeat)
        if outcome["credited_weight"] != 0:
            raise ValueError("second identical vote credited weight")
        # Feed a deliberately wrong post-state into the actual comparison.
        pre.builder_pending_payments[outcome["payment_index"]].weight += 1
        repeat["post.ssz_snappy"] = snappy.compress(pre.encode_bytes())
        try:
            check_case(lib, spec, name, repeat)
        except ValueError as error:
            if "builder_pending_payments" not in str(error):
                raise
        else:
            raise ValueError("double-credit control escaped the full-state check")
        controls.extend(["second identical vote matched complete reference state with zero credit",
                         "spurious second credit detected in payment queue"])
    if tag == "process_parent_execution_payload__full_parent_settles_builder_payment":
        pre = spec.BeaconState.decode_bytes(snappy.decompress(files["pre.ssz_snappy"]))
        block = spec.BeaconBlock.decode_bytes(snappy.decompress(files["block.ssz_snappy"]))
        # Compare both payment histories from the same official valid pre-state.
        for confirmed in (False, True):
            ref = pre.model_copy(deep=True)
            if confirmed:
                spec.process_parent_execution_payload(ref, block)
                start = pre.model_copy(deep=True)
                def decode(key, typ):
                    return typ.decode_bytes(snappy.decompress(files[key + ".ssz_snappy"]))
                data = dict(queues(start), handler="parent_execution_payload", slot=int(start.slot),
                            slotsPerEpoch=int(spec.SLOTS_PER_EPOCH))
                check_parent(lib, spec, files, decode, start, data)
            else:
                start = pre.model_copy(deep=True)
            def rotate_with_lean(state):
                data = dict(queues(state), handler="builder_pending_payments", slot=int(state.slot),
                            slotsPerEpoch=int(spec.SLOTS_PER_EPOCH), increment=int(spec.EFFECTIVE_BALANCE_INCREMENT),
                            validators=[dict(activationEpoch=int(v.activation_epoch), exitEpoch=int(v.exit_epoch),
                                             effectiveBalance=int(v.effective_balance)) for v in state.validators])
                apply_output(spec, state, "builder_pending_payments", replay(lib, data))
            for _ in range(2):
                boundary = spec.Slot((int(ref.slot) // int(spec.SLOTS_PER_EPOCH) + 1) * int(spec.SLOTS_PER_EPOCH))
                spec.process_slots(ref, boundary)
                with patch.object(spec, "process_builder_pending_payments", side_effect=rotate_with_lean) as rotate:
                    spec.process_slots(start, boundary)
                    rotate.assert_called_once()
                if start.encode_bytes() != ref.encode_bytes():
                    raise ValueError(f"divergence at epoch boundary {boundary} after parent confirmation={confirmed}")
            controls.append(f"two complete epoch rollovers after {'confirmed' if confirmed else 'unconfirmed'} parent")
    return controls
