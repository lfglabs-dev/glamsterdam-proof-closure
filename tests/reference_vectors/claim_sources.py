"""Navigation for reviewers, independent of pass/fail accounting."""
import ast
import inspect


def source_manifest(spec):
    mappings = [
        ("single settlement", "settle_slot_bid_lifecycle",
         ["apply_parent_execution_payload", "settle_builder_payment", "process_builder_pending_payments"],
         ["builder_pending_payments", "builder_pending_withdrawals"]),
        ("supply neutrality", "t_7732_no_eth_minting",
         ["can_builder_cover_bid", "get_pending_balance_to_withdraw_for_builder", "apply_withdrawals"],
         ["builders[].balance", "builder_pending_withdrawals"]),
        ("exact pending withdrawal", "t_7732_payment_guarantee",
         ["process_execution_payload_bid", "apply_parent_execution_payload", "process_builder_pending_payments"],
         ["builder_pending_withdrawals[].fee_recipient", "builder_pending_withdrawals[].amount",
          "builder_pending_withdrawals[].builder_index"]),
        ("bid coverage", "can_builder_cover_bid",
         ["process_execution_payload_bid", "can_builder_cover_bid", "get_pending_balance_to_withdraw_for_builder"],
         ["builders[].balance", "builder_pending_payments", "builder_pending_withdrawals"]),
        ("no double counting", "accrue_attester_weight",
         ["process_attestation", "get_attestation_participation_flag_indices", "is_attestation_same_slot"],
         ["builder_pending_payments[].weight", "current_epoch_participation", "previous_epoch_participation"]),
        ("frame", "process_parent_payload_if_full", ["apply_parent_execution_payload"],
         ["untouchedCl projection of the modeled payment step"]),
        ("exit initiation", "can_builder_exit",
         ["process_builder_exit_request", "get_pending_balance_to_withdraw_for_builder"],
         ["builders[].withdrawable_epoch"]),
        ("same-slot commitment", "is_canonical_full_slot_payload", ["process_parent_execution_payload"],
         ["latest_execution_payload_bid.block_hash"]),
        ("slashing on pinned spec", "slash_validator_pending_payments",
         ["slash_validator", "apply_parent_execution_payload"],
         ["builder_pending_payments", "latest_execution_payload_bid.value", "builder_pending_withdrawals"]),
        ("slashing under proposed fix", "apply_parent_payment_patched", [],
         ["pendingWithdrawals in separate patched model"]),
    ]
    functions = sorted({fn for _, _, names, _ in mappings for fn in names})
    definitions = ast.parse(inspect.getsource(spec)).body
    locations = {node.name: [node.lineno, node.end_lineno] for node in definitions
                 if isinstance(node, ast.FunctionDef) and node.name in functions}
    if set(functions) != set(locations):
        raise ValueError("claim-critical function missing from generated pinned reference")
    return {"python_module": spec.__name__, "python_source_lines": locations,
            "claims": {name: {"lean": lean, "python": names, "observables": fields}
                       for name, lean, names, fields in mappings}}
