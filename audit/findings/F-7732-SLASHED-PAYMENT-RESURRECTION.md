# F-7732-SLASHED-PAYMENT-RESURRECTION: Revoked Slashed Proposer Payment Resurrected After 2+ Missed Epochs

- **Target Repository**: `ethereum/consensus-specs`
- **Pinned Commit / Tag**: `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`, Oct 19, 2026)
- **Affected File**: `specs/gloas/beacon-chain.md` (`slash_validator` lines 1579-1581 and `apply_parent_execution_payload` lines 1799-1814)
- **Formal Refutation**: `Glamsterdam.Gloas7732.Spec.f_7732_slashed_payment_resurrection_refuter`
- **Patched Theorem**: `Glamsterdam.Gloas7732.Spec.t_7732_slashed_no_resurrection`
- **Reproducible `pyspec` Test**: [`tests/pyspec/test_slashed_proposer_payment_resurrection.py`](../../tests/pyspec/test_slashed_proposer_payment_resurrection.py)

## Root Cause

1. In `process_block` (`specs/gloas/beacon-chain.md:1760-1772`), `process_execution_payload_bid` runs before `process_operations`. It stores the committed bid (`bid.value > 0`) in `state.latest_execution_payload_bid` and creates an entry in `state.builder_pending_payments[payment_index]`.
2. In PR `#5719`, `slash_validator` (`specs/gloas/beacon-chain.md:1579-1581`) was updated so that if the proposer slashes itself in `process_operations`, its pending builder payment is revoked:
   ```python
   if slashed_index == state.latest_block_header.proposer_index:
       payment_index = SLOTS_PER_EPOCH + state.slot % SLOTS_PER_EPOCH
       state.builder_pending_payments[payment_index] = BuilderPendingPayment.empty()
   ```
   However, `slash_validator` does not zero `state.latest_execution_payload_bid.value`.
3. When a child block later builds on the parent's full execution payload (`bid.parent_block_hash == parent_bid.block_hash`), `process_parent_execution_payload` calls `apply_parent_execution_payload` (`specs/gloas/beacon-chain.md:1799-1814`):
   - If `parent_epoch` is in `current_epoch` or `previous_epoch`, `settle_builder_payment(state, payment_index)` reads the cleared `BuilderPendingPayment.empty()` (`amount == 0`) and does not pay the slashed proposer.
   - If 2+ epoch boundaries of missed slots elapsed (`parent_epoch < get_previous_epoch(state)`, added in PR `#5170`), `apply_parent_execution_payload` executes `elif parent_bid.value > 0:` and appends a `BuilderPendingWithdrawal` using `state.latest_execution_payload_bid.value` directly.

## Impact

1. **Slashed Proposer Payment Bypass and Builder Balance Deduction**: Immediately after `process_parent_execution_payload` in the child block, `process_withdrawals` sweeps `state.builder_pending_withdrawals`, deducts `parent_bid.value` from `state.builders[builder_index].balance`, and pays the self-slashed proposer's `fee_recipient` in `state.payload_expected_withdrawals`.
2. **Builder Exit Denial of Service**: Because `apply_parent_execution_payload` appends the resurrected withdrawal before `for_ops(requests.builder_exits, process_builder_exit_request)`, any legitimate `BuilderExitRequest` in `parent_execution_requests` sees `get_pending_balance_to_withdraw_for_builder(state, builder_index) > 0` (`beacon-chain.md:2380`) and is silently rejected.

## Recommended Fix

Zero `state.latest_execution_payload_bid.value` in `slash_validator` when `slashed_index == state.latest_block_header.proposer_index`:

```diff
     if slashed_index == state.latest_block_header.proposer_index:
         payment_index = SLOTS_PER_EPOCH + state.slot % SLOTS_PER_EPOCH
         state.builder_pending_payments[payment_index] = BuilderPendingPayment.empty()
+        state.latest_execution_payload_bid.value = Gwei(0)
```
