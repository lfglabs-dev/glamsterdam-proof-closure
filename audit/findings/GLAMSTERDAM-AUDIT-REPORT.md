# Glamsterdam Formal Verification & Specification Audit Report (v3 - Ground-Truth Verified)

- **Repository:** `lfglabs-dev/glamsterdam-proof-closure`
- **Toolchain:** Lean `4.31.0` + `turbo-lean` (`7c845ed4dde081eeaf5c78df3b1a750ee66a5ba8`)
- **Pinned Execution Specs:** `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e` (`src/ethereum/forks/amsterdam/`)
- **Pinned Consensus Specs:** `ethereum/consensus-specs` @ `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`, `specs/gloas/beacon-chain.md` & `specs/gloas/fork.md`)
- **Verification Status:** 60/60 formal guarantees and 10/10 verified specification edge-case findings kernel-checked (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`), 61/61 source mappings mechanically verified against 23 SHA256-locked vendored upstream files (`scripts/verify_ground_truth.py`), and 100% agreement on C-ABI + AST-extracted upstream Python differential tests (`pytest tests/ -v`).

---

## 0. First-Principles Formal Verification Scope (Consensus & Execution Core)

### 0.1 Consensus Layer (`Gloas EIP-7732` + `EIP-8282`, `Glamsterdam/Gloas7732/Spec.lean`)

1. **Supply Neutrality / No ETH Minting (`t_7732_single_settlement`, `t_7732_no_eth_minting`, `t_7732_builder_withdrawal_no_underflow`)**:
   - Every committed builder bid (`process_execution_payload_bid`, `specs/gloas/beacon-chain.md:2162-2216`) is settled **at most once** across `apply_parent_execution_payload` (`settle_builder_payment:1538-1544`, `1784-1831`) and `process_builder_pending_payments` (`1719-1732`) across all four `ChildConfirmationTiming` cases (`notConfirmed`, `confirmedSameEpoch`, `confirmedNextEpoch`, `confirmedAfterTwoEpochs`).
   - Because `can_builder_cover_bid` (`1184-1193`) enforces `builder.balance >= MIN_DEPOSIT_AMOUNT + pending_to_withdraw + bid.value` (`t_7732_builder_solvency`), `apply_withdrawals` (`1997-2007`) debits the builder's Beacon Chain balance 1-for-1 without saturation clipping (`postBuilderBalance + settled = builderBalance`). Relative to pre-Gloas consensus issuance and EIP-1559 burn, builder bid settlement is strictly supply-neutral.
2. **Proposer Payment Guarantee (`t_7732_payment_guarantee`)**:
   - Whenever a committed builder bid has `bidValue > 0` and the block is either confirmed by the child block (`timing ≠ .notConfirmed` via `apply_parent_execution_payload`) or accumulates attestation weight `attestedWeight ≥ quorum` (`process_builder_pending_payments`), the proposer's `fee_recipient` is guaranteed to receive an exact `BuilderPendingWithdrawal` of `amount = bidValue`.
3. **Unconditional Quorum Weight Anti-Double-Counting (`t_7732_quorum_no_double_count`, `t_7732_quorum_weight_unconditional`)**:
   - In `process_attestation` (`specs/gloas/beacon-chain.md:2396-2481`), the participation gate `will_set_new_flag and had_no_participation` (`2447-2467`) guarantees unconditionally across any sequence of attestations in an epoch that each validator contributes `effective_balance` to `payment.weight` at most once.
4. **Same-Slot Unbundling Resistance (`t_7732_same_slot_unbundling`)**:
   - Because `process_execution_payload_bid` (`2162-2216`) commits the slot's beacon block to `state.latest_execution_payload_bid.block_hash = bid.block_hash` and `process_parent_execution_payload` (`1841-1854`) accepts a full execution payload for that slot if and only if `child_bid.parent_block_hash == parent_bid.block_hash`, under `A-SAME-SLOT-UNBUNDLING-BOUNDARY` no canonical block at slot `N` other than the builder's committed payload can include a private transaction known only to the builder prior to payload reveal.
5. **Consensus Frame Preservation & Exit Safety (`t_7732_frame`, `t_7732_deferred_exec_equiv_empty`, `t_7732_exit_safety`, `t_8282_7732_queue_safety`)**:
   - All Gloas builder payment and parent payload transitions preserve untouched Consensus Layer state (`validatorRegistryRoot`, `blsToExecutionRoot`, `syncCommitteeRoot`), and `process_builder_exit_request` (`2368-2384`) only initiates exit when `pending_to_withdraw == 0`.

### 0.2 Execution Layer (`EIP-8246`, `EIP-8037/8038/2780/7778`, `ElCore.lean`, `Eip8246/Spec.lean`, `Gas/Spec.lean`)

1. **State Tracker Rollback & `NoEmptyAccountLeaves` Preservation (`t_common_checkpoint_rollback`, `restore_tx_state_writes_exact`, `no_empty_account_leaves_preserved`)**:
   - Every `state_tracker.py` account mutator (`modify_state` at `state_tracker.py:591-603`, `move_ether` at `state_tracker.py:606-638`, `create_ether` at `state_tracker.py:640-660`, `set_account_balance` at `state_tracker.py:663-684`, `increment_nonce` at `state_tracker.py:686-703`, `set_code` at `state_tracker.py:705-729`) routes through `modify_state`, destroying any account that becomes empty (`destroy_account` at `state_tracker.py:466-491`) and preserving `NoEmptyAccountLeaves`, under which `account_exists` (`state_tracker.py:342-359`) and `is_account_alive` (`state_tracker.py:403-421`) coincide (`account_exists_iff_alive_of_no_empty_leaves`).
2. **2D State-Gas Reservoir, Spill, and System-Transaction Accounting (`spill_invariant_preserved_by_meter_ops`, `t_8037_allocate_evm_gas_sound`, `t_7778_8037_dual_cap`, `t_8037_sys_tx_reservoir_sound`)**:
   - All `GasMeter` operations (`vm/gas.py:260-647`) preserve `meterSpillInvariant`, `allocate_evm_gas` (`vm/gas.py:1105-1138`) partitions transaction gas across `execution_gas` and `state_gas_reservoir`, and `process_unchecked_system_transaction` (`fork.py:100-114, 724-780`) initializes `GasMeter(gas_left=30,000,000, state_gas_left=1,566,720, state_gas_baseline=1,566,720)` from `SYSTEM_TRANSACTION_GAS` and `StateGasCosts.STORAGE_SET * SYSTEM_MAX_SSTORES_PER_CALL`.
3. **EIP-8246 `SELFDESTRUCT` Conservation & Cleanup (`t_8246_balance_preserved`, `t_8246_selfdestruct_conservation`, `t_8246_no_state_gas_refund`, `t_8246_storage_clears_recorded_in_bal`)**:
   - `clear_account_preserving_balance` (`state_tracker.py:494-516`) zeroes nonce, clears code, and wipes storage while preserving balance (deleting the account leaf iff `balance == 0`).

### 0.3 Compositional Multi-Frame Call-Tree Gas Core & Refill-Variant Proofs (`FV-CORE`, `Glamsterdam/Gas/CallTree.lean`)

1. **`SSTORE` Sentry Reservoir Exclusion (`t_calltree_sstore_sentry_excludes_reservoir`)**:
   - In `sstore` (`vm/instructions/storage.py:68-162`, specifically `lines 100-105`), `check_gas(evm, max(gas_cost, GasCosts.CALL_STIPEND + 1))` (`GasCosts.CALL_STIPEND = 2,300` at `vm/gas.py:84`) checks only `gas_left` and ignores `state_gas_left`. Thus any `2,300`-stipend value call or fixed-grant call with `gasLeft <= 2300` halts with `OutOfGasError` across every `ForkSchedule` regardless of `stateGasLeft`.
2. **In-Frame Upper-Bound Invariant (`t_calltree_a1_frame_bound`) & Universal Fixed-Grant Starvation (`t_calltree_e1_fixed_grant_starvation`)**:
   - Within a single frame (`vm/gas.py:379-616`), `charge_gas_from_meter`, `charge_state_gas_from_meter`, and `credit_state_gas_refund` preserve `post.gasLeft + post.stateGasSpilled <= m.gasLeft + m.stateGasSpilled`.
   - When `stateGasLeft = 0` (`tx.gas <= 2^24`), a fixed-grant child frame (`gasLeft = 50,000`) writing one fresh slot (`0 -> 1`) succeeds on `osaka` and deterministically OOGs across every Amsterdam refill variant (`D0`, `D1`, `D3`, `D4`, `D13`, `D13R`, `D13S`).
3. **Multi-Frame Refill-Variant Characterization & Adversarial Counterexamples (`D0`, `D1`, `D3`, `D4`, `D13`, `D13R`, `D13S`)**:
   - **Dirty-Clear `M2` (`t_calltree_e3_m2_dirty_clear_band_and_d13r_break`, `t_calltree_d13r_introduces_new_t1_band`)**: Proves that `amsterdamD0` creates a silent-failure band when a parent sets `k` temporary slots, calls a child that OOGs due to the `k * 97,920` state-gas spill, and clears the `k` slots afterward; `amsterdamD1` and `amsterdamD13` eliminate this band; and `amsterdamD13R` both re-opens `T2f` on any post-clear subcall and introduces a brand-new `T1` silent-failure band when `0 -> 1 -> 0` happens before `CALL(GAS)`.
   - **Revert-Restore `M3` (`t_calltree_e3_m3_revert_restore_catch_band`)**: Proves that `amsterdamD0`, `amsterdamD1`, and `amsterdamD4` return a reverting child's `stateGasSpilled` to `parent.gasLeft` (funding parent `try/catch` execution), whereas `amsterdamD3`, `amsterdamD13`, `amsterdamD13R`, and `amsterdamD13S` defer the reverted child's spill to transaction settlement.
   - **Refutation of `D13S` across Cross-Sibling `M4`, Helper-Clear `T2`, and Failed `CREATE` `T6` (`t_calltree_e3_m4_sibling_underflow_and_d13s_break`, `t_calltree_d13s_reopens_t2_on_child_clear`, `t_calltree_d13s_failed_create_strands_gas`)**: Proves three distinct adversarial counterexamples in `amsterdamD13S` (`childExcess = child.stateGasLeft - child.stateGasBaseline` capped repayment on child success, plus uncapped `settle_top_frame` at top-frame exit): (a) when Child 1 writes `0 -> 1` and Child 2 clears `1 -> 0` inside a `[g1, g2]` gas-measurement window, Child 2 exits with `childExcess = 97,920 > 0`, jumping `parent.gasLeft` by `+97,920` (`g2 > g1`); (b) when the `k` context slots in `T2` are cleared inside a helper subcall after the main child call fails, the helper exits with `childExcess = k * 97,920 > 0` and re-opens the `T2` silent-failure band; and (c) after a failed `CREATE` (`vm/instructions/system.py:59-186`), `credit_state_gas_refund` runs after `incorporate_child`, stranding `183,600` execution gas in `stateGasLeft` mid-frame even after subsequent successful subcalls (starving post-`CREATE` execution work and causing mid-frame `OutOfGasError` before `settle_top_frame` is ever reached).

---

## 1. Calibrated Specification Edge-Case Matrix (10 Verified Findings)

| ID | Domain | Finding | Calibrated Severity | Formal Refuter / Proof in Lean 4.31 |
| :--- | :--- | :--- | :--- | :--- |
| **1.1** | CL (`EIP-7732`) | `F-7732-SLASHED-PAYMENT-RESURRECTION` | **Medium-High** (Confirmed Cross-Epoch Inconsistency) | `f_7732_slashed_payment_resurrection_refuter`, `t_7732_composed_trace_resurrects_slashed_payment` |
| **1.2** | CL (`EIP-7732`) | `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` | **Medium** (Confirmed Fork-Boundary Bug) | `f_7732_fork_slot_availability_refuter` |
| **1.3** | CL (`EIP-7732`) | `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` | **Low-Medium** (Confirmed Ring-Buffer Wrap Bug) | `f_7732_availability_ring_buffer_clobber_refuter` |
| **1.4** | CL (`EIP-8282`) | `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP` | **Medium** (Cross-Function Ordering Divergence) | `f_8282_topup_credential_prefix_drop_refuter` |
| **1.5** | CL (`EIP-7732`) | `F-7732-FORK-ONBOARD-CROSS-CREDENTIAL` | **Informational / Low** (`fork.md:115-117` Dual of 1.4) | `f_7732_fork_onboard_cross_credential_refuter` |
| **2.1** | EL (`EIP-8246` + `7928`) | `F-8246-BAL-STORAGE-CLEARS-IGNORED` | **High** (Confirmed Multi-Tx & System-Tx BAL Desync) | `f_8246_bal_storage_clears_ignored_refuter`, `t_8246_bal_tx_block_state_desync`, `t_8246_storage_clears_recorded_in_bal` |
| **2.2** | EL (`EIP-8038` + `7778`) | `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS` | **Medium** (Confirmed EIP-7778 Normative Tension) | `f_8038_7778_sstore_reset_refuter` |
| **2.3** | EL (`EIP-8037` + `7702`) | `F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE` | **Low** (Defense-in-Depth on Unpruned Pre-States) | `f_8037_7702_delegation_exists_vs_alive_refuter`, `t_8037_7702_delegation_exists_eq_alive_under_invariant` |
| **2.4** | EL (`EIP-8246`) | `F-8246-UNCHECKED-SYS-TX-DROPS-ACCOUNTS-TO-DELETE` | **Low** (Defense-in-Depth Cleanup Omission) | `f_8246_unchecked_sys_tx_drops_deletes_refuter` |
| **2.5** | EL (`EIP-2780` + `7928`) | `F-2780-7928-SET-DELEGATION-OOG-OMITS-RECIPIENT-READ` | **Low** (Pre-Dispatch OOG Ordering in `create_evm`) | `f_2780_7928_set_delegation_oog_omits_recipient_refuter` |

---

## 2. Consensus Layer Edge-Case Details (`specs/gloas/beacon-chain.md` & `specs/gloas/fork.md` @ `aa16bb4c`)

### 1.1 `F-7732-SLASHED-PAYMENT-RESURRECTION` (Medium-High)
- **Location:** `specs/gloas/beacon-chain.md:1549-1582` (`slash_validator`, specifically `lines 1578-1581`) & `1784-1831` (`apply_parent_execution_payload`, specifically `lines 1799-1814`)
- **Root Cause:** In `slash_validator` (`beacon-chain.md:1578-1581`), pending builder payments for blocks proposed by `slashed_index` are cleared by iterating over `state.builder_pending_payments`:
  ```python
  for payment_index, payment in enumerate(state.builder_pending_payments):
      if payment.proposer_index == slashed_index:
          state.builder_pending_payments[payment_index] = BuilderPendingPayment.empty()
  ```
  However, `slash_validator` does not zero `state.latest_execution_payload_bid.value`. When 2+ missed epochs elapse before the next beacon block confirms the parent payload (`parent_epoch < get_previous_epoch(state)`), `apply_parent_execution_payload` (`lines 1805-1814`) takes the `elif parent_bid.value > 0:` branch and appends a `BuilderPendingWithdrawal` directly from `state.latest_execution_payload_bid.value`, resurrecting the slashed proposer's revoked payment and blocking any `BuilderExitRequest` in `requests.builder_exits` (`line 1826` -> `line 2380`).
- **Formal Refuter & Patch Proof:** `f_7732_slashed_payment_resurrection_refuter`, `t_7732_composed_trace_resurrects_slashed_payment`, and `t_7732_slashed_no_resurrection` in `Glamsterdam/Gloas7732/Spec.lean`.
- **Resolution Options:** Either (Option A) also zero `state.latest_execution_payload_bid.value = Gwei(0)` when `state.latest_block_header.proposer_index == slashed_index` in `slash_validator`, or (Option B, First-Principles Simplification) remove lines `1578-1581` from `slash_validator` so builder bid settlement depends purely on canonical payload confirmation or attestation quorum.

### 1.2 `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` (Medium)
- **Location:** `specs/gloas/fork.md:135-232` (`upgrade_to_gloas`, specifically `lines 198-200`) & `specs/gloas/beacon-chain.md:1339-1387` (`get_attestation_participation_flag_indices`, specifically `lines 1366-1368`)
- **Root Cause:** `upgrade_to_gloas` initializes all `SLOTS_PER_HISTORICAL_ROOT` entries of `state.execution_payload_availability` to `0b1`, including index `s_fork % SLOTS_PER_HISTORICAL_ROOT` (`state.slot` at the fork boundary). Because `upgrade_to_gloas` runs inside `process_slots` *after* `process_slot(s_fork - 1)` has already executed, `process_slot` at `s_fork` (`beacon-chain.md:1608-1623`) clears `(s_fork + 1) % SLOTS_PER_HISTORICAL_ROOT` and never clears `s_fork % SLOTS_PER_HISTORICAL_ROOT` to `0b0`. If the fork-slot block's payload is withheld, `execution_payload_availability[s_fork % SLOTS_PER_HISTORICAL_ROOT]` remains `0b1`.
- **Formal Refuter:** `f_7732_fork_slot_availability_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.

### 1.3 `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` (Low-Medium)
- **Location:** `specs/gloas/beacon-chain.md:1608-1623` (`process_slot`, specifically `lines 1620-1622`) & `1784-1831` (`apply_parent_execution_payload`, specifically `line 1829`)
- **Root Cause:** During `state_transition` from `parent_slot` to `block.slot`, `process_slots` runs `process_slot` at `block.slot - 1`, which sets `execution_payload_availability[block.slot % SLOTS_PER_HISTORICAL_ROOT] = Boolean(False)`. Immediately afterward, `process_block` calls `apply_parent_execution_payload` (if the parent payload was full), which sets `execution_payload_availability[parent_slot % SLOTS_PER_HISTORICAL_ROOT] = Boolean(True)`. When `block.slot - parent_slot == k * SLOTS_PER_HISTORICAL_ROOT` (`64` skipped slots in `minimal`, `8192` in `mainnet`), `apply_parent_execution_payload` overwrites the child block's own availability bit back to `True`.
- **Formal Refuter:** `f_7732_availability_ring_buffer_clobber_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.

### 1.4 `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP` & 1.5 `F-7732-FORK-ONBOARD-CROSS-CREDENTIAL` (Cross-Function Ordering Divergence)
- **Location:** `specs/gloas/beacon-chain.md:2334-2361` (`process_builder_deposit_request`) vs `specs/gloas/fork.md:70-120` (`onboard_builders_from_pending_deposits`)
- **Root Cause:** The two builder deposit functions in `v1.7.0-beta.4` check `pubkey in builder_pubkeys` and `is_builder_withdrawal_credential` (`0xB0`) in opposite orders:
  1. `process_builder_deposit_request` (`beacon-chain.md:2334-2361`, processing `BUILDER_DEPOSIT_REQUEST_TYPE = 0x03` requests emitted by `BUILDER_DEPOSIT_CONTRACT_ADDRESS` in `src/ethereum/forks/amsterdam/fork.py:901`) checks `if not is_builder_withdrawal_credential(request.withdrawal_credentials): return` at `line 2336` *before* checking `if request.pubkey not in builder_pubkeys:` at `line 2340`. Consequently, a top-up to an already-registered builder submitted with zeroed/non-`0xB0` credentials is silently dropped on the CL (`f_8282_topup_credential_prefix_drop_refuter`).
  2. Conversely, `onboard_builders_from_pending_deposits` (`fork.md:70-120`, onboarding from the shared pre-fork `state.pending_deposits` queue) checks `if deposit.pubkey not in builder_pubkeys:` at `line 92` *before* checking `if not is_builder_withdrawal_credential(deposit.withdrawal_credentials):` at `line 93`. Consequently, its `else:` branch at `lines 115-117` credits any subsequent pending deposit whose `pubkey` is already in `builder_pubkeys` even if that deposit carried `0x01`/`0x02` validator credentials (`f_7732_fork_onboard_cross_credential_refuter`).

---

## 3. Execution Layer Edge-Case Details (`src/ethereum/forks/amsterdam/` @ `16898000`)

### 2.1 `F-8246-BAL-STORAGE-CLEARS-IGNORED` (High: `EIP-8246` + `EIP-7928` Interaction)
- **Location:** `src/ethereum/forks/amsterdam/state_tracker.py:494-516` (`clear_account_preserving_balance`), `state_tracker.py:518-540` (`destroy_storage`), & `state_tracker.py:793-846` (`incorporate_tx_into_block`) vs `src/ethereum/forks/amsterdam/block_access_lists.py:760-825` (`update_builder_from_tx`)
- **Root Cause:** When `destroy_storage(tx_state, address)` is called (either via `destroy_account` when an account becomes empty or via `clear_account_preserving_balance` at end-of-transaction cleanup for `accounts_to_delete`), it moves all keys in `tx_state.storage_writes[address]` to `tx_state.storage_reads` (`state_tracker.py:535-537`), deletes `tx_state.storage_writes[address]` (`line 538`), and adds `address` to `tx_state.storage_clears` (`line 539`). At transaction commit, `incorporate_tx_into_block` calls `update_builder_from_tx(builder, tx_state)` (`state_tracker.py:817`) before merging `tx_state` into `block_state`. However, `update_builder_from_tx` (`block_access_lists.py:813-825`) only iterates over `tx_state.storage_writes` and completely ignores `tx_state.storage_clears`.
- **Reachable Desynchronization Paths:**
  1. **Two-Transaction Block Desync (`t_8246_bal_tx_block_state_desync`, `t_8246_storage_clears_recorded_in_bal`)**: `Tx 1` writes a non-zero slot `(A, k) = 42` (`BlockState` and BAL both record `42`). `Tx 2` wipes `A`'s storage via `destroy_storage(tx_state, A)`. `incorporate_tx_into_block` pops `A` from `block_state.storage_writes` and adds `A` to `block_state.storage_clears` (so post-block storage is `0`), while `update_builder_from_tx` ignores `tx_state.storage_clears` and leaves `42` as the final post-block value in the Block Access List.
  2. **Shared `block_access_index` System Transactions (`fork.py:815-921`)**: Multiple system transactions share `block_access_index = 0` (pre-execution) or `len(transactions) + 1` (post-execution).
- **Formal Refuter & Patch Proof:** `f_8246_bal_storage_clears_ignored_refuter`, `t_8246_bal_patched_sound`, `t_8246_bal_tx_block_state_desync`, and `t_8246_storage_clears_recorded_in_bal` in `Glamsterdam/Eip8246/Spec.lean`.

### 2.2 `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS` (Medium: `EIP-8037` + `EIP-8038` + `EIP-7778` Interaction)
- **Location:** `src/ethereum/forks/amsterdam/vm/instructions/storage.py:68-162` (`sstore`) & `src/ethereum/forks/amsterdam/vm/gas.py:1163-1228` (`settle_transaction_gas`)
- **Root Cause:** When a zero storage slot transitions `0 -> X -> 0` within the same transaction (`original_value == 0`), the second `SSTORE` directly restores `StateGasCosts.STORAGE_SET` (`97,920`) via `credit_state_gas_refund` (`storage.py:151`), but places `GasCosts.STORAGE_WRITE` (`10,000`) into `evm.gas_meter.refund_counter` (`storage.py:139`). Consequently, `settle_transaction_gas` (`vm/gas.py:1211-1222`) does not deduct the `10,000` dirty-reset refund from block `execution_gas_used`, and clips the sender refund whenever `gas_used_before_refund < 50,000`.
- **Formal Refuter:** `f_8038_7778_sstore_reset_refuter` in `Glamsterdam/Gas/Spec.lean`.

### 2.3 `F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE` (Low - Defense-in-Depth on Unpruned Pre-States)
- **Location:** `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:295-296` (`set_delegation`)
- **Root Cause & Invariant Boundary:** All other `StateGasCosts.NEW_ACCOUNT` (`183,600`) charging sites check `not is_account_alive(tx_state, addr)`, whereas `set_delegation` (`eoa_delegation.py:295`) checks `if not account_exists(tx_state, authority):`. Because all `state_tracker.py` mutators route through `modify_state` and preserve `NoEmptyAccountLeaves` (`no_empty_account_leaves_preserved` in `Glamsterdam/Common/ElCore.lean`), the two predicates are identical on any state starting from a pruned `PreState` (`t_8037_7702_delegation_exists_eq_alive_under_invariant`). They diverge only if `PreState` itself contains an unpruned `EMPTY_ACCOUNT` leaf (as in raw state-test fixtures), modeled by `f_8037_7702_delegation_exists_vs_alive_refuter`.

### 2.4 `F-8246-UNCHECKED-SYS-TX-DROPS-ACCOUNTS-TO-DELETE` (Low - Defense-in-Depth)
- **Location:** `src/ethereum/forks/amsterdam/fork.py:724-780` (`process_unchecked_system_transaction`) vs `1045-1102` (`process_transaction`, specifically `lines 1088-1089`)
- **Root Cause:** `process_unchecked_system_transaction` calls `process_top_level` (`line 765`) and passes `system_tx_state` directly to `incorporate_tx_into_block` (`line 772`) without iterating over `system_tx_output.accounts_to_delete` via `clear_account_preserving_balance` (`fork.py:1088-1089`).
- **Formal Refuter:** `f_8246_unchecked_sys_tx_drops_deletes_refuter` in `Glamsterdam/Eip8246/Spec.lean`.

### 2.5 `F-2780-7928-SET-DELEGATION-OOG-OMITS-RECIPIENT-READ` (Low)
- **Location:** `src/ethereum/forks/amsterdam/vm/interpreter.py:133-196` (`create_evm`, specifically `line 161`) & `235-288` (`process_top_level`, specifically `lines 264-277`)
- **Root Cause:** In `process_top_level` (`interpreter.py:265`), `create_evm` runs inside `try: ... except ExceptionalHalt:` *before* `get_account(tx_env.state, tx_env.target)` is called at `line 277`. Inside `create_evm` (`line 161`), `set_delegation(block_env, tx_env, gas_meter)` is called before `create_evm` returns. If `set_delegation` raises `OutOfGasError` (a subclass of `ExceptionalHalt`, e.g., when charging `StateGasCosts.NEW_ACCOUNT = 183,600`), `process_top_level` catches `ExceptionalHalt` at `line 269`, calls `restore_tx_state` and `restore_state_gas_to_entry`, and returns early at `line 275` before `get_account(tx_env.state, tx_env.target)` at `line 277` is reached. Thus `tx_env.target` is omitted from `tx_state.account_reads` even though the sender paid `COLD_ACCOUNT_ACCESS` (`3,000` gas) for `tx.to` in intrinsic gas.
- **Formal Refuter:** `f_2780_7928_set_delegation_oog_omits_recipient_refuter` in `Glamsterdam/Gas/Spec.lean`.
