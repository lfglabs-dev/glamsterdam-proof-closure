"""
Reproducible pyspec tests for F-7732-SLASHED-PAYMENT-RESURRECTION
Target commit: ethereum/consensus-specs @ aa16bb4c156184e9548a997d53efaf2a228a6304 (v1.7.0-beta.4)
Upstream functions:
- `slash_validator` (`specs/gloas/beacon-chain.md:1549-1582`)
- `process_builder_pending_payments` (`specs/gloas/beacon-chain.md:1719-1732`)
- `apply_parent_execution_payload` (`specs/gloas/beacon-chain.md:1784-1831`)
- `process_builder_exit_request` (`specs/gloas/beacon-chain.md:2368-2384`)

Drop-in test 1 -> tests/core/pyspec/eth_consensus_specs/test/gloas/sanity/test_blocks.py
Drop-in test 2 -> tests/core/pyspec/eth_consensus_specs/test/gloas/block_processing/test_process_parent_execution_payload.py
Standalone pytest execution -> `pytest tests/pyspec/test_slashed_proposer_payment_resurrection.py`
"""
from __future__ import annotations

import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:
    from eth_consensus_specs.test.context import spec_state_test, with_gloas_and_later
    from eth_consensus_specs.test.helpers.attester_slashings import (
        get_valid_attester_slashing_by_indices,
    )
    from eth_consensus_specs.test.helpers.block import (
        build_empty_block,
        build_empty_block_for_next_slot,
    )
    from eth_consensus_specs.test.helpers.EpochProcessing import (
        next_epoch_with_full_participation,
    )
    from eth_consensus_specs.test.helpers.keys import builder_privkeys
    from eth_consensus_specs.test.helpers.state import state_transition_and_sign_block
except ImportError:
    def with_gloas_and_later(fn):
        return fn

    def spec_state_test(fn):
        return fn


# ==============================================================================
# 1. Sanity / Multi-block drop-in test (for `test_blocks.py`)
# Combines `test_builder_payment_removed_when_proposer_slashes_itself`
# (`beacon-chain.md:1579-1581`) with `test_builder_payment_after_missed_epochs`
# (`beacon-chain.md:1805-1814`).
# ==============================================================================
@with_gloas_and_later
@spec_state_test
def pyspec_builder_payment_removed_when_proposer_slashes_itself_after_missed_epochs(spec, state):
    """
    Test that a proposer who slashes itself in the block carrying a positive
    builder bid still does not receive the builder payment when the canonical
    payload is confirmed after 2+ epochs of missed blocks (older than
    previous_epoch).
    """
    # Advance to get finalization
    for _ in range(4):
        next_epoch_with_full_participation(spec, state)
    assert state.finalized_checkpoint.epoch == 2

    # Build Block 1 with a non-zero value bid from a builder AND a self-slashing
    block_1 = build_empty_block_for_next_slot(spec, state)
    builder_index = 0
    value = spec.Gwei(1000000)  # 0.001 ETH
    fee_recipient = spec.ExecutionAddress(b"\xab" * 20)
    block_hash = spec.Hash32(b"\x42" * 32)

    bid = block_1.body.signed_execution_payload_bid.message
    bid.block_hash = block_hash
    bid.builder_index = builder_index
    bid.value = value
    bid.fee_recipient = fee_recipient
    bid.execution_requests_root = spec.hash_tree_root(spec.ExecutionRequests())

    signature = spec.get_execution_payload_bid_signature(
        state, bid, builder_privkeys[builder_index]
    )
    block_1.body.signed_execution_payload_bid = spec.SignedExecutionPayloadBid(
        message=bid,
        signature=signature,
    )
    state.builders[builder_index].balance = spec.MIN_DEPOSIT_AMOUNT + value

    # Proposer slashes itself in Block 1
    attester_slashing = get_valid_attester_slashing_by_indices(
        spec, state, [block_1.proposer_index], signed_1=True, signed_2=True
    )
    block_1.body.attester_slashings = spec.AttesterSlashings(data=[attester_slashing])

    yield "pre", state

    # Process Block 1:
    # 1. process_execution_payload_bid sets latest_execution_payload_bid.value = value
    #    and populates builder_pending_payments[payment_idx]
    # 2. process_attester_slashings -> slash_validator clears builder_pending_payments[payment_idx]
    #    (but leaves latest_execution_payload_bid.value == value on unpatched v1.7.0-beta.4)
    signed_block_1 = state_transition_and_sign_block(spec, state, block_1)

    assert state.validators[block_1.proposer_index].slashed
    payment_idx = spec.SLOTS_PER_EPOCH + block_1.slot % spec.SLOTS_PER_EPOCH
    assert state.builder_pending_payments[payment_idx] == spec.BuilderPendingPayment()

    pre_builder_balance = state.builders[builder_index].balance

    # Advance 2+ epochs with missed slots so parent_epoch < get_previous_epoch(state),
    # then confirm Block 1's payload in Block 2 (bid.parent_block_hash == block_hash).
    block_1_epoch = spec.compute_epoch_at_slot(block_1.slot)
    block_2_slot = spec.compute_start_slot_at_epoch(block_1_epoch + 2) + 1
    block_2 = build_empty_block(spec, state, slot=block_2_slot)
    block_2.body.signed_execution_payload_bid.message.parent_block_hash = block_hash
    signed_block_2 = state_transition_and_sign_block(spec, state, block_2)

    yield "blocks", [signed_block_1, signed_block_2]
    yield "post", state

    # Confirm apply_parent_execution_payload ran
    parent_slot_index = bid.slot % spec.SLOTS_PER_HISTORICAL_ROOT
    assert state.execution_payload_availability[parent_slot_index]

    # Expected invariant: slashed proposer's revoked payment must NOT be resurrected
    # and swept by Block 2's process_withdrawals, and builder must NOT be charged.
    # (FAILS on v1.7.0-beta.4 / aa16bb4c: builder is charged `value` and withdrawal
    #  is emitted in `state.payload_expected_withdrawals`!)
    assert state.builders[builder_index].balance == pre_builder_balance
    assert not any(
        w.address == fee_recipient and w.amount == value
        for w in state.payload_expected_withdrawals
    )


# ==============================================================================
# 2. Block-processing drop-in test with BuilderExitRequest DoS
#    (for `test_process_parent_execution_payload.py`)
# ==============================================================================
@with_gloas_and_later
@spec_state_test
def pyspec_process_parent_execution_payload__older_than_previous_epoch_slashed_proposer_builder_exit(
    spec, state
):
    """
    When the parent block's proposer was slashed (revoking its pending builder
    payment), confirming that parent payload after 2+ missed epochs must not
    resurrect the payment from `latest_execution_payload_bid.value` or block
    a legitimate `BuilderExitRequest` in `parent_execution_requests`.
    """
    builder_index = 0
    value = spec.Gwei(50_000_000)
    fee_recipient = spec.ExecutionAddress(b"\xab" * 20)
    builder = state.builders[builder_index]
    requests = spec.ExecutionRequests(
        builder_exits=spec.BuilderExitRequests(
            data=[
                spec.BuilderExitRequest(
                    source_address=builder.execution_address, pubkey=builder.pubkey
                )
            ]
        )
    )

    parent_slot = spec.Slot(spec.SLOTS_PER_EPOCH - 1)
    parent_proposer = spec.get_beacon_proposer_index(state, parent_slot)
    state.latest_block_header.slot = parent_slot
    state.latest_block_header.proposer_index = parent_proposer
    state.latest_execution_payload_bid.slot = parent_slot
    state.latest_execution_payload_bid.fee_recipient = fee_recipient
    _commit_parent_requests(spec, state, requests, value=value, builder_index=builder_index)

    # Simulate proposer self-slashing during parent block's `process_operations`
    spec.slash_validator(state, parent_proposer)
    payment_idx = spec.SLOTS_PER_EPOCH + parent_slot % spec.SLOTS_PER_EPOCH
    assert state.builder_pending_payments[payment_idx] == spec.BuilderPendingPayment()

    # Cross two epoch boundaries so parent_epoch < get_previous_epoch(state)
    spec.process_slots(state, 2 * spec.SLOTS_PER_EPOCH)
    state.finalized_checkpoint.epoch = spec.Epoch(1)
    block = build_empty_block_for_next_slot(spec, state)
    block.body.parent_execution_requests = requests
    spec.process_slots(state, block.slot)

    assert spec.compute_epoch_at_slot(parent_slot) < spec.get_previous_epoch(state)
    assert spec.is_active_builder(state, builder_index)
    assert spec.get_pending_balance_to_withdraw_for_builder(state, builder_index) == 0
    pre_pending_withdrawals_len = len(state.builder_pending_withdrawals)

    yield from run_parent_execution_payload_processing(spec, state, block)

    # Slashed proposer payment must NOT be resurrected, and builder exit must succeed.
    # (FAILS on v1.7.0-beta.4 / aa16bb4c: withdrawal is resurrected and builder exit is blocked!)
    assert len(state.builder_pending_withdrawals) == pre_pending_withdrawals_len
    assert not spec.is_active_builder(state, builder_index)


# ==============================================================================
# 3. Standalone Mechanically Executable Test Against Vendored `beacon-chain.md`
# ==============================================================================
def test_standalone_vendored_pyspec_reproducer():
    """
    Executes both scenarios (resurrected payment + blocked `BuilderExitRequest`)
    directly against the markdown-extracted Python functions from
    `vendor/upstreams/consensus_specs/specs/gloas/beacon-chain.md`.
    """
    import importlib.util
    import re

    diff_path = ROOT / "tests" / "differential" / "test_glamsterdam_differential.py"
    spec_mod = importlib.util.spec_from_file_location("test_glamsterdam_differential", diff_path)
    diff_mod = importlib.util.module_from_spec(spec_mod)
    spec_mod.loader.exec_module(diff_mod)
    VENDOR_BEACON_MD = diff_mod.VENDOR_BEACON_MD
    load_vendored_gloas_specs = diff_mod.load_vendored_gloas_specs

    env = load_vendored_gloas_specs()
    md_text = VENDOR_BEACON_MD.read_text(encoding="utf-8")
    for block in re.findall(r"```python\n(.*?)```", md_text, flags=re.DOTALL):
        if block.lstrip().startswith(("def initiate_builder_exit(", "def process_builder_exit_request(")):
            exec(compile(block, str(VENDOR_BEACON_MD), "exec"), env)

    BuilderPendingPayment = env["BuilderPendingPayment"]
    BuilderPendingWithdrawal = env["BuilderPendingWithdrawal"]
    slash_validator = env["slash_validator"]
    process_builder_pending_payments = env["process_builder_pending_payments"]
    apply_parent_execution_payload = env["apply_parent_execution_payload"]

    spe = 8
    env["SLOTS_PER_EPOCH"] = spe
    env["MIN_BUILDER_WITHDRAWABILITY_DELAY"] = 64
    env["compute_epoch_at_slot"] = lambda slot: slot // spe
    env["get_current_epoch"] = lambda st: st.slot // spe
    env["get_previous_epoch"] = lambda st: max(0, (st.slot // spe) - 1)
    env["get_total_active_balance"] = lambda _st: 32_000_000_000_000
    env["initiate_validator_exit"] = lambda _st, _idx: None
    env["decrease_balance"] = lambda _st, _idx, _amt: None
    env["increase_balance"] = lambda _st, _idx, _amt: None
    env["get_beacon_proposer_index"] = lambda st: st.latest_block_header.proposer_index
    for req_fn in (
        "process_deposit_request",
        "process_withdrawal_request",
        "process_consolidation_request",
        "process_builder_deposit_request",
    ):
        env[req_fn] = lambda _st, _op: None

    parent_slot = spe - 1
    proposer_idx = 7
    bid_value = 50_000_000
    fee_recipient = 0xAB
    builder_pubkey = 0x9999
    builder_exec_addr = 0xCAFE

    payments = [BuilderPendingPayment.empty() for _ in range(2 * spe)]
    payments[spe + (parent_slot % spe)] = BuilderPendingPayment(
        weight=0,
        withdrawal=BuilderPendingWithdrawal(
            fee_recipient=fee_recipient, amount=bid_value, builder_index=0
        ),
        proposer_index=proposer_idx,
    )

    builder_obj = type(
        "Builder",
        (),
        {
            "pubkey": builder_pubkey,
            "execution_address": builder_exec_addr,
            "balance": 1_000_000_000 + bid_value,
            "deposit_epoch": 0,
            "withdrawable_epoch": env["FAR_FUTURE_EPOCH"],
        },
    )()

    state = type(
        "BeaconState",
        (),
        {
            "slot": parent_slot,
            "finalized_checkpoint": type("Cp", (), {"epoch": 1})(),
            "validators": {
                proposer_idx: type(
                    "Validator",
                    (),
                    {"slashed": False, "withdrawable_epoch": 0, "effective_balance": 32_000_000_000},
                )()
            },
            "builders": [builder_obj],
            "slashings": [0] * 64,
            "builder_pending_payments": payments,
            "builder_pending_withdrawals": [],
            "latest_block_header": type(
                "Header", (), {"slot": parent_slot, "proposer_index": proposer_idx}
            )(),
            "latest_execution_payload_bid": type(
                "Bid",
                (),
                {
                    "value": bid_value,
                    "fee_recipient": fee_recipient,
                    "builder_index": 0,
                    "block_hash": 0x4242,
                },
            )(),
            "execution_payload_availability": [False] * 64,
            "latest_block_hash": 0,
        },
    )()

    # Step 1: Slashing clears `builder_pending_payments[payment_idx]`
    slash_validator(state, proposer_idx)
    assert state.builder_pending_payments[spe + (parent_slot % spe)] == BuilderPendingPayment.empty()
    assert env["get_pending_balance_to_withdraw_for_builder"](state, 0) == 0

    # Step 2: Advance across 2 epoch boundaries (`parent_epoch = 0 < previous_epoch = 1`)
    process_builder_pending_payments(state)
    process_builder_pending_payments(state)
    state.slot = 2 * spe + 1

    # Step 3: Child block confirms parent payload with a valid `BuilderExitRequest`
    exit_req = type(
        "BuilderExitRequest",
        (),
        {"source_address": builder_exec_addr, "pubkey": builder_pubkey},
    )()
    requests = type(
        "ExecutionRequests",
        (),
        {
            "deposits": [],
            "withdrawals": [],
            "consolidations": [],
            "builder_deposits": [],
            "builder_exits": [exit_req],
        },
    )()
    apply_parent_execution_payload(state, requests)

    # Confirm the unpatched v1.7.0-beta.4 bug:
    # 1) Slashed proposer's withdrawal is resurrected from `parent_bid.value`
    assert state.builder_pending_withdrawals == [
        BuilderPendingWithdrawal(fee_recipient=fee_recipient, amount=bid_value, builder_index=0)
    ]
    # 2) Because the resurrected withdrawal makes `get_pending_balance_to_withdraw_for_builder(state, 0) != 0`
    #    before `process_builder_exit_request` runs at line 1826, the builder's exit request is blocked!
    assert env["is_active_builder"](state, 0) is True
