# F-7732-SLASHED-PAYMENT-RESURRECTION: Revoked Slashed Proposer Payment Resurrected After 2+ Missed Epochs

- **Target Repository**: `ethereum/consensus-specs`
- **Pinned Commit / Tag**: `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`, Oct 19, 2026)
- **Affected File**: `specs/gloas/beacon-chain.md` (`slash_validator` lines `1549-1582`, specifically `1578-1581`, and `apply_parent_execution_payload` lines `1784-1831`, specifically `1799-1814`)
- **Formal Refutation**: `Glamsterdam.Gloas7732.Spec.f_7732_slashed_payment_resurrection_refuter` and `Glamsterdam.Gloas7732.Spec.t_7732_composed_trace_resurrects_slashed_payment`
- **Patched Theorem**: `Glamsterdam.Gloas7732.Spec.t_7732_slashed_no_resurrection`
- **Reproducible `pyspec` Test**: [`tests/pyspec/test_slashed_proposer_payment_resurrection.py`](../../tests/pyspec/test_slashed_proposer_payment_resurrection.py)

## Root Cause

1. In `process_block` (`specs/gloas/beacon-chain.md:1754-1772`), `process_execution_payload_bid` (`line 1766`, defined at `lines 2162-2216`) runs before `process_operations` (`line 1770`). When `bid.value > 0`, it populates `state.builder_pending_payments[SLOTS_PER_EPOCH + bid.slot % SLOTS_PER_EPOCH]` (`proposer_index = get_beacon_proposer_index(state)`) and caches `state.latest_execution_payload_bid = bid` (`line 2215`).
2. In `slash_validator` (`specs/gloas/beacon-chain.md:1578-1581`), pending builder payments for blocks proposed by `slashed_index` are cleared by iterating over `state.builder_pending_payments`:
   ```python
   # [New in Gloas:EIP7732]
   # Remove pending builder payments for blocks proposed by the slashed validator
   for payment_index, payment in enumerate(state.builder_pending_payments):
       if payment.proposer_index == slashed_index:
           state.builder_pending_payments[payment_index] = BuilderPendingPayment.empty()
   ```
   However, when `slashed_index` is the proposer of `state.latest_block_header` (`state.latest_block_header.proposer_index == slashed_index`), `slash_validator` does **not** zero `state.latest_execution_payload_bid.value`.
3. When a child block later confirms the parent's full execution payload (`bid.parent_block_hash == parent_bid.block_hash`), `process_parent_execution_payload` (`lines 1841-1854`) calls `apply_parent_execution_payload` (`lines 1784-1831`):
   - If `parent_epoch == get_current_epoch(state)` (`lines 1799-1801`) or `parent_epoch == get_previous_epoch(state)` (`lines 1802-1804`), `settle_builder_payment(state, payment_index)` reads the cleared `BuilderPendingPayment.empty()` (`payment.withdrawal.amount == 0`) and does not queue a withdrawal.
   - If 2+ epoch boundaries of missed slots elapsed (`parent_epoch < get_previous_epoch(state)`), the slot's `BuilderPendingPayment` entry has been rotated out of `state.builder_pending_payments` by two calls to `process_builder_pending_payments` (`lines 1719-1732`), and `apply_parent_execution_payload` falls into `elif parent_bid.value > 0:` (`lines 1805-1814`), appending a `BuilderPendingWithdrawal` directly from `state.latest_execution_payload_bid.value`.

## Protocol Design Note & Impact

- **Protocol Policy vs. Supply Invariant**: Note that this edge case does **not** mint ETH or double-spend (`t_7732_single_settlement` and `t_7732_no_eth_minting` hold because `process_builder_pending_payments` evicted the cleared entry without settling it, and the builder's balance covered `parent_bid.value` at bid acceptance). Whether a slashed proposer whose committed payload becomes canonical should have its builder payment cancelled at all is a protocol design question.
- **Inconsistency in `v1.7.0-beta.4`**: Because `v1.7.0-beta.4` explicitly cancels pending builder payments in `slash_validator` (`lines 1578-1581`), leaving `state.latest_execution_payload_bid.value > 0` creates an inconsistency between the `< 2` missed-epoch path (where the payment is cancelled) and the `>= 2` missed-epoch path (where the payment is resurrected from `parent_bid.value` and blocks any `BuilderExitRequest` in `requests.builder_exits` at `line 1826` because `get_pending_balance_to_withdraw_for_builder(state, builder_index) != 0` at `line 2380`).

## Options to Resolve the Inconsistency

1. **Option A (Enforce Slashed-Proposer Payment Cancellation Across All Epoch Delays)**: In `slash_validator` (`specs/gloas/beacon-chain.md:1578-1581`), also zero `state.latest_execution_payload_bid.value = Gwei(0)` when `state.latest_block_header.proposer_index == slashed_index` (or gate `elif parent_bid.value > 0:` at `line 1805` on `and not state.validators[state.latest_block_header.proposer_index].slashed`):
   ```diff
        # [New in Gloas:EIP7732]
        # Remove pending builder payments for blocks proposed by the slashed validator
        for payment_index, payment in enumerate(state.builder_pending_payments):
            if payment.proposer_index == slashed_index:
                state.builder_pending_payments[payment_index] = BuilderPendingPayment.empty()
   +    if state.latest_block_header.proposer_index == slashed_index:
   +        state.latest_execution_payload_bid.value = Gwei(0)
   ```
2. **Option B (First-Principles Simplification — Decouple Builder Payment Settlement from Slashing)**: Remove lines `1578-1581` from `slash_validator` altogether so builder bid settlement depends purely on canonical payload confirmation (`apply_parent_execution_payload`) or attestation quorum (`process_builder_pending_payments`), while proposer misbehavior is penalized solely through standard validator slashing penalties (`beacon-chain.md:1564-1566`).
