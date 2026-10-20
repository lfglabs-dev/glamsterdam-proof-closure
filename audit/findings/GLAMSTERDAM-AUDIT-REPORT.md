# Glamsterdam Formal Verification & Specification Audit Report

- **Repository:** `lfglabs-dev/glamsterdam-proof-closure`
- **Toolchain:** Lean `4.31.0` + `turbo-lean` (`7c845ed4dde081eeaf5c78df3b1a750ee66a5ba8`)
- **Pinned Execution Specs:** `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e` (`src/ethereum/forks/amsterdam/`)
- **Pinned Consensus Specs:** `ethereum/consensus-specs` @ `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`, `specs/gloas/beacon-chain.md` & `specs/gloas/fork.md`)
- **Verification Status:** 31/31 guarantees kernel-checked (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`, `0` vacuous specs), 100% agreement on C-ABI + Python differential test suite (`tests/differential/test_glamsterdam_differential.py`).

---

## 1. Consensus Layer Findings (`Gloas EIP-7732` + `EIP-8282`, `v1.7.0-beta.4` @ `aa16bb4c`)

### 1.1 `F-7732-SLASHED-PAYMENT-RESURRECTION` (High)
- **Location:** `specs/gloas/beacon-chain.md:1579-1581` (`slash_validator`) & `1799-1814` (`apply_parent_execution_payload`)
- **Root Cause:** In PR #5719, `slash_validator` clears `state.builder_pending_payments[payment_index]` when `payment.proposer_index == slashed_index`, but does not zero `state.latest_execution_payload_bid.value`. When 2+ missed epochs elapse before the next beacon block confirms the parent payload (`parent_epoch < get_previous_epoch(state)`), `apply_parent_execution_payload` (PR #5170) takes the `elif parent_bid.value > 0:` branch and reads `parent_bid.value` directly from `state.latest_execution_payload_bid`, resurrecting the slashed proposer's revoked payment into `state.builder_pending_withdrawals`.
- **Formal Refuter & Patch Proof:** `f_7732_slashed_payment_resurrection_refuter` & `t_7732_slashed_no_resurrection` in `Glamsterdam/Gloas7732/Spec.lean`.
- **Fix:** In `slash_validator`, if `slashed_index == state.latest_block_header.proposer_index`, also set `state.latest_execution_payload_bid.value = Gwei(0)`.

### 1.2 `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` (Medium-High)
- **Location:** `specs/gloas/fork.md:198-200` (`upgrade_to_gloas`) & `specs/gloas/beacon-chain.md:1366-1368` (`get_attestation_participation_flag_indices`)
- **Root Cause:** `upgrade_to_gloas` initializes all `SLOTS_PER_HISTORICAL_ROOT` entries of `state.execution_payload_availability` to `0b1`, including index `s_fork % SLOTS_PER_HISTORICAL_ROOT` (`state.slot` at the fork boundary). Because `upgrade_to_gloas` runs inside `process_slots` *after* `process_slot(s_fork - 1)` has already executed, `process_slot` never clears `s_fork % SLOTS_PER_HISTORICAL_ROOT` to `False`. If the first Gloas block at `s_fork` has an EMPTY payload (`bid.parent_block_hash != parent_bid.block_hash`) and `s_fork + 1` is skipped, `execution_payload_availability[s_fork % SLOTS_PER_HISTORICAL_ROOT]` remains `0b1` (`True`), inverting `TIMELY_HEAD_FLAG_INDEX` rewards for attestations at `s_fork + 1`.
- **Formal Refuter:** `f_7732_fork_slot_availability_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.
- **Fix:** In `upgrade_to_gloas`, set `post.execution_payload_availability[pre.slot % SLOTS_PER_HISTORICAL_ROOT] = 0b0`.

### 1.3 `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` (Medium)
- **Location:** `specs/gloas/beacon-chain.md:1620-1622` (`process_slot`) & `1829` (`apply_parent_execution_payload`)
- **Root Cause:** During `state_transition` from `parent_slot` to `block.slot`, `process_slots` runs `process_slot` at `block.slot - 1`, which clears `execution_payload_availability[block.slot % SLOTS_PER_HISTORICAL_ROOT] = Boolean(False)`. Immediately afterward, `process_block` calls `apply_parent_execution_payload` (if the parent payload was full), which sets `execution_payload_availability[parent_slot % SLOTS_PER_HISTORICAL_ROOT] = Boolean(True)`. When `block.slot - parent_slot == k * SLOTS_PER_HISTORICAL_ROOT` (64 slots in `minimal`, 8192 slots in `mainnet`), `apply_parent_execution_payload` clobbers the child block's own availability bit back to `True` before the child block's payload is ever revealed.
- **Formal Refuter:** `f_7732_availability_ring_buffer_clobber_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.

### 1.4 `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP` (Medium)
- **Location:** `specs/gloas/beacon-chain.md:2334-2361` (`process_builder_deposit_request`) vs `EIP-8282` (lines 134, 159) and `specs/gloas/fork.md:92-118` (`onboard_builders_from_pending_deposits`)
- **Root Cause:** `EIP-8282` specifies that when `request.pubkey` is already in `state.builders`, the deposit is a balance top-up (`builder.balance += request.amount`) and `withdrawal_credentials` and `signature` are not validated (matching `onboard_builders_from_pending_deposits` in `fork.md:92-118`). However, `process_builder_deposit_request` checks `if not is_builder_withdrawal_credential(request.withdrawal_credentials): return` at line 2336 *before* checking `if request.pubkey not in builder_pubkeys:` at line 2340. Any top-up to an existing builder submitted with non-`0xB0` credentials (e.g., zeroed credentials) is silently dropped on the CL while the ETH remains burned in the EL deposit contract.
- **Formal Refuter:** `f_8282_topup_credential_prefix_drop_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.
- **Fix:** Move the `is_builder_withdrawal_credential` check inside the `if request.pubkey not in builder_pubkeys:` branch.

### 1.5 `F-7732-CROSS-BLOCK-PROPOSER-SLASHING-ORDERING` (Low-Medium)
- **Location:** `specs/gloas/beacon-chain.md:1759-1770` (`process_block`)
- **Root Cause:** `process_block` executes `process_parent_execution_payload` (line 1759) and `process_withdrawals` (line 1762) *before* `process_operations` (line 1770, which calls `slash_validator`). Consequently, if a proposer of slot `N` (whose payload was full) is slashed in slot `N + 1`, its builder payment is settled into `builder_pending_withdrawals` and deducted into `payload_expected_withdrawals` before `slash_validator` runs, whereas if slot `N`'s payload was empty or the slashing was included in slot `N` itself, the payment is revoked.

### 1.6 `F-7732-FORK-ONBOARD-CROSS-CREDENTIAL` (Medium, Upstream Issue #5735)
- **Location:** `specs/gloas/fork.md:70-120` (`onboard_builders_from_pending_deposits`)
- **Root Cause:** In `onboard_builders_from_pending_deposits`, once a pending deposit with `0xB0` credentials registers `pubkey` in `state.builders`, any subsequent pending deposit in `state.pending_deposits` with the same `pubkey` hits the `else:` branch (lines 115-117) and credits `state.builders[builder_index].balance += deposit.amount` even if that subsequent deposit carried `0x01`/`0x02` validator withdrawal credentials.

---

## 2. Execution Layer Findings (`EIP-8246` & `Gas EIP-8037/8038/2780/7778`, `execution-specs` @ `16898000`)

### 2.1 `F-8246-BAL-STORAGE-CLEARS-IGNORED` (High: `EIP-8246` + `EIP-7928` Interaction)
- **Location:** `src/ethereum/forks/amsterdam/state_tracker.py:518-540` (`destroy_storage`) & `816-830` (`incorporate_tx_into_block`) vs `src/ethereum/forks/amsterdam/block_access_lists.py:813-825` (`update_builder_from_tx`)
- **Root Cause:** When `destroy_storage(tx_state, address)` is called (by `clear_account_preserving_balance`, `destroy_account`, or `process_create`), it moves all keys in `tx_state.storage_writes[address]` to `tx_state.storage_reads`, deletes `tx_state.storage_writes[address]`, and adds `address` to `tx_state.storage_clears`. At transaction commit, `incorporate_tx_into_block` calls `update_builder_from_tx(builder, tx_state)` before merging into `block_state`. However, `update_builder_from_tx` only iterates over `tx_state.storage_writes` and completely ignores `tx_state.storage_clears`.
  - **Case A (Pre-existing storage wiped):** If `address` had a non-zero storage slot `k -> V` at the start of the `block_access_index` (e.g., via deployment over a storage-bearing account in `process_create`, or an empty storage-bearing account touched and destroyed by `modify_state`), `destroy_storage` wipes the slot in `BlockState` (`block.storage_clears.add(address)`), but `update_builder_from_tx` records no `StorageChange(idx, 0)` and no `storage_read` for `k` in the Block Access List.
  - **Case B (Same-`block_access_index` write then clear):** If an earlier sub-operation under the same `block_access_index` recorded a `StorageChange(idx, V)` in `builder` and a subsequent operation in the same `block_access_index` calls `destroy_storage`, `remove_storage_write` is never called, leaving a stale non-zero `StorageChange` in the BAL.
- **Formal Refuter & Patch Proof:** `f_8246_bal_storage_clears_ignored_refuter` & `t_8246_bal_patched_sound` in `Glamsterdam/Eip8246/Spec.lean`.

### 2.2 `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS` (Medium: `EIP-8037` + `EIP-8038` + `EIP-7778` Interaction)
- **Location:** `src/ethereum/forks/amsterdam/vm/instructions/storage.py:120-152` (`sstore`) & `src/ethereum/forks/amsterdam/vm/gas.py:1211-1222` (`settle_transaction_gas`) vs `EIP-7778` (`eip-7778.md:43`)
- **Root Cause:** When a zero storage slot transitions `0 -> X -> 0` within the same transaction (`original_value == 0`):
  1. The first `SSTORE` charges `10,000` execution gas (`STORAGE_WRITE`) and `97,920` state gas (`STORAGE_SET`).
  2. The second `SSTORE` (`X -> 0`) directly restores the `97,920` state gas via `credit_state_gas_refund(evm.gas_meter, StateGasCosts.STORAGE_SET)`, but puts the `10,000` execution gas (`STORAGE_WRITE`) into `evm.gas_meter.refund_counter += int(GasCosts.STORAGE_WRITE)`.
  This asymmetric restoration has two consequences:
  - **Block Gas Accounting (`EIP-7778`):** `settle_transaction_gas` (`vm/gas.py:1217-1222`) computes `execution_gas_used = max(gas_used_before_refund - settled_state_gas_used, calldata_floor)` without subtracting `refund_counter`. Thus the `10,000` dirty-reset refund is never deducted from block execution gas, contradicting `eip-7778.md:43` (*"Storage discounts that reflect actual reduced computational work (e.g., warm storage access, reverting to original values) remain applied to block gas accounting"*).
  - **User 20% Refund Cap Clipping:** Because `credit_state_gas_refund` restores the `97,920` state gas directly to `state_gas_left` / `gas_left`, `gas_used_before_refund` is reduced by `97,920` before computing `gas_refund = min(gas_used_before_refund // 5, refund_counter)`. On any transaction whose pre-refund execution gas is under `50,000` (e.g., `25,200` gas), `gas_used_before_refund // 5 = 5,040 < 10,000`, so `4,960` gas of the temporary `STORAGE_WRITE` charge is clipped and lost.
- **Formal Refuter:** `f_8038_7778_sstore_reset_refuter` in `Glamsterdam/Gas/Spec.lean`.

### 2.3 `F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE` (Medium)
- **Location:** `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:295` (`set_delegation`) & `src/ethereum/forks/amsterdam/vm/interpreter.py:178` (`create_evm`)
- **Root Cause:** Across `execution-specs`, four `StateGasCosts.NEW_ACCOUNT` charging sites (`call`, `generic_create`, `selfdestruct`, `charge_value_transfer_to_non_alive_account`) check `not is_account_alive(tx_state, addr)` (`account is not None and account != EMPTY_ACCOUNT`). However:
  - `set_delegation` (`eoa_delegation.py:295`) checks `if not account_exists(tx_state, authority):` (`get_account_optional is not None`); and
  - `create_evm` (`interpreter.py:178`) checks `if get_pre_state_account(tx_env.state, current_target) == EMPTY_ACCOUNT:` (reading `pre_state` rather than `tx_state`).
- **Formal Refuter:** `f_8037_7702_delegation_exists_vs_alive_refuter` in `Glamsterdam/Gas/Spec.lean`.

### 2.4 `F-8246-UNCHECKED-SYS-TX-DROPS-ACCOUNTS-TO-DELETE` (Low-Medium)
- **Location:** `src/ethereum/forks/amsterdam/fork.py:724-780` (`process_unchecked_system_transaction`) vs `1088-1089` (`process_transaction`)
- **Root Cause:** `process_transaction` iterates over `tx_output.accounts_to_delete` and calls `clear_account_preserving_balance(tx_env.state, address)` before calling `incorporate_tx_into_block`. In contrast, `process_unchecked_system_transaction` calls `process_top_level` and immediately calls `incorporate_tx_into_block` without processing `system_tx_output.accounts_to_delete`.

### 2.5 `F-8037-SYS-TX-GAS-LIMIT-INVARIANT` (Low)
- **Location:** `src/ethereum/forks/amsterdam/fork.py:756-761` (`process_unchecked_system_transaction`) vs `EIP-8037` (`eip-8037.md:293`)
- **Root Cause:** `process_unchecked_system_transaction` sets `tx_env.gas_limit = SYSTEM_TRANSACTION_GAS` (`30,000,000`) while granting `execution_gas_grant = 30,000,000` and `state_gas_reservoir = 1,566,720` (`31,566,720` total), violating `eip-8037.md:293` (`SYSTEM_CALL_GAS_LIMIT = 30,000,000 + 1,566,720 = 31,566,720`) and the invariant `gas_limit >= execution_gas_grant + state_gas_reservoir`.

### 2.6 `F-2780-7928-SET-DELEGATION-OOG-OMITS-RECIPIENT-READ` (Low)
- **Location:** `src/ethereum/forks/amsterdam/vm/interpreter.py:160-196` (`create_evm`)
- **Root Cause:** When `set_delegation` raises `OutOfGasError` at line 161 of `create_evm`, `create_evm` aborts before line 185/189 where `tx.to` (`current_target`) is read via `get_account_optional` / `get_account`. Although `tx.to`'s `COLD_ACCOUNT_ACCESS` (`3,000` gas) was already paid in intrinsic gas (`eip-2780.md:146`), `tx.to` is never added to `tx_state.account_reads` and is omitted from the Block Access List.
