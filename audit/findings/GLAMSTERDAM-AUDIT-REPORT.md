# Glamsterdam Formal Verification & Specification Audit Report (v2 - Post-Adversarial Arbitration)

- **Repository:** `lfglabs-dev/glamsterdam-proof-closure`
- **Toolchain:** Lean `4.31.0` + `turbo-lean` (`7c845ed4dde081eeaf5c78df3b1a750ee66a5ba8`)
- **Pinned Execution Specs:** `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e` (`src/ethereum/forks/amsterdam/`)
- **Pinned Consensus Specs:** `ethereum/consensus-specs` @ `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`, `specs/gloas/beacon-chain.md` & `specs/gloas/fork.md`)
- **Verification Status:** 41/41 guarantees and 12/12 findings kernel-checked (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`, `0` vacuous specs), 100% agreement on C-ABI + Python differential test suite (`tests/differential/test_glamsterdam_differential.py`).
- **Adversarial Review Panel:** Audited and red-teamed by 4 independent hostile reviewers (`Fable 5.1`, `GPT-6.1 Sol High`, `GPT-6 Astra`, `Gemini 4 Argon`) role-playing the upstream authors to challenge reachability, preconditions, and severity ratings.

---

## 0. Executive Summary & Calibrated Severity Matrix

| ID | Domain | Finding | Initial Severity | Final Calibrated Severity (Arbiter) | Formal Refuter / Proof in Lean 4.31 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1.1** | CL (`EIP-7732`) | `F-7732-SLASHED-PAYMENT-RESURRECTION` | High | **Medium-High** (Confirmed Cross-PR Logic Bug) | `f_7732_slashed_payment_resurrection_refuter`, `t_7732_composed_trace_resurrects_slashed_payment` |
| **1.2** | CL (`EIP-7732`) | `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` | Medium-High | **Medium** (Confirmed Fork-Boundary Bug) | `f_7732_fork_slot_availability_refuter` |
| **1.3** | CL (`EIP-7732`) | `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` | Medium | **Low-Medium** (Confirmed Ring-Buffer Wrap Bug) | `f_7732_availability_ring_buffer_clobber_refuter` |
| **1.4** | CL (`EIP-8282`) | `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP` | Medium | **Medium** (Confirmed Spec-vs-EIP Divergence) | `f_8282_topup_credential_prefix_drop_refuter` |
| **1.5** | CL (`EIP-7732`) | `F-7732-EARLIER-SLOT-PROPOSER-SLASHING-NOT-CLEARED` | Low-Medium | **Medium** (Confirmed `slash_validator` Oversight) | `f_7732_earlier_slot_proposer_slashing_refuter` |
| **1.6** | CL (`EIP-7732`) | `F-7732-FORK-ONBOARD-CROSS-CREDENTIAL` | Medium | **Informational / Low** (Upstream Issue #5735 Cross-Ref) | `f_7732_fork_onboard_cross_credential_refuter` |
| **2.1** | EL (`EIP-8246` + `7928`) | `F-8246-BAL-STORAGE-CLEARS-IGNORED` | High | **High** (Confirmed Multi-Tx & System-Tx BAL Corruption) | `f_8246_bal_storage_clears_ignored_refuter`, `t_8246_bal_tx_block_state_desync` |
| **2.2** | EL (`EIP-8038` + `7778`) | `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS` | Medium | **Medium** (Confirmed EIP-7778 Normative Tension) | `f_8038_7778_sstore_reset_refuter` |
| **2.3** | EL (`EIP-8037` + `7702`) | `F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE` | Medium | **Low** (Defense-in-Depth / `set_account_balance` Edge Case) | `f_8037_7702_delegation_exists_vs_alive_refuter`, `set_account_balance_zero_creates_empty_leaf` |
| **2.4** | EL (`EIP-8246`) | `F-8246-UNCHECKED-SYS-TX-DROPS-ACCOUNTS-TO-DELETE` | Low-Medium | **Low** (Defense-in-Depth Cleanup Omission) | `f_8246_unchecked_sys_tx_drops_deletes_refuter` |
| **2.5** | EL (`EIP-8037`) | `F-8037-SYS-TX-GAS-LIMIT-INVARIANT` | Low | **Low** (`SYS_TX_GAS_LIMIT` Bypasses `allocate_evm_gas`) | `f_8037_sys_tx_gas_limit_invariant_refuter` |
| **2.6** | EL (`EIP-2780` + `7928`) | `F-2780-7928-SET-DELEGATION-OOG-OMITS-RECIPIENT-READ` | Low | **Low** (OOG Ordering Before `get_account(tx_state, to)`) | `f_2780_7928_set_delegation_oog_omits_recipient_refuter` |

---

## 1. Consensus Layer Findings (`Gloas EIP-7732` + `EIP-8282`, `v1.7.0-beta.4` @ `aa16bb4c`)

### 1.1 `F-7732-SLASHED-PAYMENT-RESURRECTION` (Medium-High)
- **Location:** `specs/gloas/beacon-chain.md:1579-1581` (`slash_validator`) & `1799-1814` (`apply_parent_execution_payload`)
- **Root Cause:** In PR #5719, `slash_validator` clears `state.builder_pending_payments[payment_index]` when `slashed_index == state.latest_block_header.proposer_index`, but does not zero `state.latest_execution_payload_bid.value`. When 2+ missed epochs elapse before the next beacon block confirms the parent payload (`parent_epoch < get_previous_epoch(state)`), `apply_parent_execution_payload` (PR #5170) takes the `elif parent_bid.value > 0:` branch and reads `parent_bid.value` directly from `state.latest_execution_payload_bid`, resurrecting the slashed proposer's revoked payment into `state.builder_pending_withdrawals`.
- **Author Defense vs. Arbiter Verdict:**
  - *Author Defense:* In any child block $B_c$, `apply_parent_execution_payload` (line 1759) runs *before* `process_operations` (line 1770), so a slashing included in $B_c$ cannot trigger `slash_validator` before `apply_parent_execution_payload`.
  - *Arbiter Verdict:* **Confirmed Reachable.** In the parent block $B_p$ itself, `process_block_header` (line 1757) sets `state.latest_block_header.proposer_index = block.proposer_index`, `process_execution_payload_bid` (line 1766) populates `latest_execution_payload_bid` and `builder_pending_payments[payment_index]`, and `process_operations` (line 1770) executes slashings in $B_p.\text{body}$. When $B_p$ includes an `AttesterSlashing` (or `ProposerSlashing`) whose slashed set contains $B_p$'s own proposer (e.g., an attester slashing from an intersecting committee), `slash_validator` runs inside $B_p$ at line 1579, clears `builder_pending_payments[payment_index]`, and leaves `latest_execution_payload_bid.value > 0`. If $B_p$ is followed by a 2-epoch skip (`parent_epoch < get_previous_epoch(state)`), the child block $B_c$ resurrects the slashed payment. Severity is calibrated from High to **Medium-High** due to the required combination of self-block slashing (or Fix 1.5) and a cross-epoch finality stall.
- **Formal Refuter & Patch Proof:** `f_7732_slashed_payment_resurrection_refuter`, `t_7732_composed_trace_resurrects_slashed_payment`, and `t_7732_slashed_no_resurrection` in `Glamsterdam/Gloas7732/Spec.lean`.
- **Fix:** In `slash_validator`, when clearing a proposer's pending payment, also set `state.latest_execution_payload_bid.value = Gwei(0)` if `slashed_index == state.latest_block_header.proposer_index`.

### 1.2 `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` (Medium)
- **Location:** `specs/gloas/fork.md:198-200` (`upgrade_to_gloas`) & `specs/gloas/beacon-chain.md:1366-1368` (`get_attestation_participation_flag_indices`)
- **Root Cause:** `upgrade_to_gloas` initializes all `SLOTS_PER_HISTORICAL_ROOT` entries of `state.execution_payload_availability` to `0b1`, including index `s_fork % SLOTS_PER_HISTORICAL_ROOT` (`state.slot` at the fork boundary). Because `upgrade_to_gloas` runs inside `process_slots` *after* `process_slot(s_fork - 1)` has already executed, `process_slot` at `s_fork` clears `(s_fork + 1) % SLOTS_PER_HISTORICAL_ROOT` and never clears `s_fork % SLOTS_PER_HISTORICAL_ROOT` to `0b0`.
- **Author Defense vs. Arbiter Verdict:**
  - *Author Defense:* At `s_fork`, the parent block is the last Fulu block, so `block_0` at `s_fork` has a full parent; why would `s_fork`'s own payload be empty?
  - *Arbiter Verdict:* **Confirmed.** In ePBS (`EIP-7732`), whether slot `s_fork`'s own execution payload is full or empty is decided when `s_fork`'s builder reveals (or withholds!) the payload envelope for `block_0`, and is recorded when the child block at `s_fork + 1` (or later) executes `apply_parent_execution_payload`. If the builder for `block_0` at `s_fork` withholds its payload, the child block at `s_fork + 1` builds on the empty parent (`child_bid.parent_block_hash != block_0_bid.block_hash`) and does not call `apply_parent_execution_payload`. Yet `state.execution_payload_availability[s_fork % SLOTS_PER_HISTORICAL_ROOT]` remains `0b1` (`True`) from `upgrade_to_gloas`, so `get_attestation_participation_flag_indices` (`beacon-chain.md:1366-1368`) rewards attestations at `s_fork` that set `data.index == 1` (full payload) and penalizes honest PTC-aligned attestations that set `data.index == 0` (empty payload).
- **Formal Refuter:** `f_7732_fork_slot_availability_refuter` (modeled on `AvailabilityRing` in `Glamsterdam/Gloas7732/Spec.lean`).
- **Fix:** In `upgrade_to_gloas`, set `post.execution_payload_availability[pre.slot % SLOTS_PER_HISTORICAL_ROOT] = 0b0`.

### 1.3 `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` (Low-Medium)
- **Location:** `specs/gloas/beacon-chain.md:1620-1622` (`process_slot`) & `1829` (`apply_parent_execution_payload`)
- **Root Cause:** During `state_transition` from `parent_slot` to `block.slot`, `process_slots` runs `process_slot` at `block.slot - 1`, which clears `execution_payload_availability[block.slot % SLOTS_PER_HISTORICAL_ROOT] = Boolean(False)`. Immediately afterward, `process_block` calls `apply_parent_execution_payload` (if the parent payload was full), which sets `execution_payload_availability[parent_slot % SLOTS_PER_HISTORICAL_ROOT] = Boolean(True)`. When `block.slot - parent_slot == k * SLOTS_PER_HISTORICAL_ROOT` (64 skipped slots in `minimal`, 8192 in `mainnet`), `apply_parent_execution_payload` clobbers the child block's own availability bit back to `True` before the child block's payload is ever revealed.
- **Author Defense vs. Arbiter Verdict:**
  - *Author Defense:* On `mainnet`, `SLOTS_PER_HISTORICAL_ROOT = 8192` (~27.3 hours of skipped slots), which only occurs during catastrophic chain stalls, testnets, or `minimal`-preset EEST/hive tests (`SLOTS_PER_HISTORICAL_ROOT = 64`, 8 epochs).
  - *Arbiter Verdict:* **Confirmed** (calibrated to **Low-Medium**). Directly reachable in `minimal` preset after 64 skipped slots; trivial 1-line guard (`if state.slot - parent_slot < SLOTS_PER_HISTORICAL_ROOT:`) eliminates the wrap-around clobber.
- **Formal Refuter:** `f_7732_availability_ring_buffer_clobber_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.

### 1.4 `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP` (Medium)
- **Location:** `specs/gloas/beacon-chain.md:2334-2361` (`process_builder_deposit_request`) vs `EIP-8282` (`eip-8282.md:134, 159`) and `specs/gloas/fork.md:92-118` (`onboard_builders_from_pending_deposits`)
- **Root Cause:** `EIP-8282` (`eip-8282.md:134, 159`) normatively specifies that a `BuilderDepositRequest` (`BUILDER_DEPOSIT_REQUEST_TYPE = 0x03`, emitted by `BUILDER_DEPOSIT_CONTRACT_ADDRESS` in `el_fork.py:901`) for an already-registered `pubkey` in `state.builders` is a balance top-up: *"The `amount` is credited and the record's `withdrawal_credentials` and `signature` are ignored"* (matching `onboard_builders_from_pending_deposits` in `fork.md:92-118`). However, `process_builder_deposit_request` (`beacon-chain.md:2336`) checks `if not is_builder_withdrawal_credential(request.withdrawal_credentials): return` *before* checking `if request.pubkey not in builder_pubkeys:` at line 2340. Any top-up to an existing builder submitted with dummy/zeroed `withdrawal_credentials` (`0x00...`) is silently dropped on the CL while the ETH remains locked in `BUILDER_DEPOSIT_CONTRACT_ADDRESS` on the EL.
- **Formal Refuter:** `f_8282_topup_credential_prefix_drop_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.
- **Fix:** Move `if not is_builder_withdrawal_credential(request.withdrawal_credentials): return` inside the `if request.pubkey not in builder_pubkeys:` registration branch.

### 1.5 `F-7732-EARLIER-SLOT-PROPOSER-SLASHING-NOT-CLEARED` (Medium)
- **Location:** `specs/gloas/beacon-chain.md:1579-1581` (`slash_validator`) & `1757-1770` (`process_block`)
- **Root Cause:** In `slash_validator` (PR #5719), the proposer-payment revocation check is written as:
  ```python
  if slashed_index == state.latest_block_header.proposer_index:
      payment_index = SLOTS_PER_EPOCH + state.latest_block_header.slot % SLOTS_PER_EPOCH
      state.builder_pending_payments[payment_index] = BuilderPendingPayment()
  ```
  However, in `process_block`, `process_block_header` runs at line 1757 *before* `process_operations` (line 1770) and overwrites `state.latest_block_header` with the **current** block's header (`state.latest_block_header.proposer_index = block.proposer_index`). Therefore, if proposer $P_1$ proposed block $B_1$ at slot $s_1$ (leaving a pending payment in `state.builder_pending_payments` awaiting epoch-end quorum settlement because $B_2$ built on an empty parent or after skipped slots) and a later block $B_2$ at slot $s_2 > s_1$ in the same or next epoch includes a `ProposerSlashing` or `AttesterSlashing` against $P_1$, `slashed_index == state.latest_block_header.proposer_index` evaluates `P_1 == P_2` (`False`!). $P_1$'s pending builder payment in `state.builder_pending_payments` is **never cleared** by `slash_validator` and still settles at epoch end if it reached PTC/attestation quorum!
- **Formal Refuter:** `f_7732_earlier_slot_proposer_slashing_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.
- **Fix:** In `slash_validator`, iterate over `state.builder_pending_payments` and clear every entry where `payment.proposer_index == slashed_index` (and if `slashed_index == state.latest_block_header.proposer_index`, also zero `state.latest_execution_payload_bid.value`).

### 1.6 `F-7732-FORK-ONBOARD-CROSS-CREDENTIAL` (Informational / Low - Upstream Issue #5735)
- **Location:** `specs/gloas/fork.md:70-120` (`onboard_builders_from_pending_deposits`)
- **Context & Arbiter Note:** Unlike post-fork `BuilderDepositRequest` (`0x03`, which comes from the dedicated `BUILDER_DEPOSIT_CONTRACT_ADDRESS`), pre-fork `state.pending_deposits` come from the shared validator deposit contract where credential prefixes (`0x01`/`0x02` vs `0xB0`) distinguish validator deposits from builder deposits. In `onboard_builders_from_pending_deposits`, once a `0xB0` deposit registers `pubkey` in `state.builders`, any subsequent pending deposit in `state.pending_deposits` with the same `pubkey` enters the `else:` branch (lines 115-117) and credits `state.builders[builder_index].balance` even if that deposit carried `0x01`/`0x02` credentials. This is the exact dual of Finding 1.4 and explains why upstream added the early credential check in `beacon-chain.md:2336` (tracked in `consensus-specs#5735`).
- **Formal Refuter:** `f_7732_fork_onboard_cross_credential_refuter` in `Glamsterdam/Gloas7732/Spec.lean`.

---

## 2. Execution Layer Findings (`EIP-8246` & `Gas EIP-8037/8038/2780/7778`, `execution-specs` @ `16898000`)

### 2.1 `F-8246-BAL-STORAGE-CLEARS-IGNORED` (High: `EIP-8246` + `EIP-7928` Interaction)
- **Location:** `src/ethereum/forks/amsterdam/state_tracker.py:518-540` (`destroy_storage`) & `816-830` (`incorporate_tx_into_block`) vs `src/ethereum/forks/amsterdam/block_access_lists.py:813-825` (`update_builder_from_tx`)
- **Root Cause:** When `destroy_storage(tx_state, address)` is called, it moves all keys in `tx_state.storage_writes[address]` to `tx_state.storage_reads`, deletes `tx_state.storage_writes[address]`, and adds `address` to `tx_state.storage_clears`. At transaction commit, `incorporate_tx_into_block` calls `update_builder_from_tx(builder, tx_state)` before merging `tx_state` into `block_state`. However, `update_builder_from_tx` only iterates over `tx_state.storage_writes` and completely ignores `tx_state.storage_clears`.
- **Author Defense vs. Arbiter Verdict:**
  - *Author Defense:* (1) Under `A-NO-PRE-EXISTING-STORAGE-ON-CREATE`, `process_create` cannot wipe non-zero pre-existing storage. (2) Normal transactions have distinct `block_access_index` values `1..N`, so how can an earlier write in the block be corrupted?
  - *Arbiter Verdict:* **Confirmed High Severity via Two Reachable Standard Mainnet Paths (Zero Pre-Existing Collision Storage Needed):**
    1. **Cross-Transaction `CREATE2` -> `SSTORE` (Tx 1) then `destroy_storage` (Tx 2) in the Same Block:**
       - Suppose in `Tx 1` (`block_access_index = 1`), slot `0` on address $A$ is written to `42` (`BlockState.storage_writes[A][0] = 42`, and BAL records `StorageChange(block_access_index=1, new_value=42)`).
       - In `Tx 2` (`block_access_index = 2`), `destroy_storage(tx_state, A)` is executed (for instance, $A$ had `nonce = 0, code = b""` and `Tx 2` deploys over $A$ via `process_create`, or $A$ becomes empty in `Tx 2` and `modify_state` calls `destroy_account(tx_state, A)`). `incorporate_tx_into_block` (`state_tracker.py:827-829`) pops $A$ from `block_state.storage_writes` and adds $A$ to `block_state.storage_clears` (so post-block state has `slot 0 = 0`), while `update_builder_from_tx` in `Tx 2` ignores `tx_state.storage_clears` and records **nothing** for `block_access_index = 2`! Thus the Block Access List claims the final post-block value of `(A, 0)` is `42` (from `Tx 1`), whereas `BlockState` has wiped `(A, 0)` to `0`!
    2. **Shared `block_access_index` in Pre-Execution (`idx = 0`) and Post-Execution (`idx = len(txs) + 1`) System Calls (`fork.py:815-825, 831-921`):**
       - In `apply_body` (`fork.py:815`), `builder.block_access_index` is `0` during both `process_system_transaction(BEACON_ROOTS_ADDRESS)` and `process_system_transaction(HISTORY_STORAGE_ADDRESS)`, and is `len(transactions) + 1` across `process_withdrawals` and all four post-block system transactions (`DEPOSIT`, `WITHDRAWAL_REQUEST`, `CONSOLIDATION_REQUEST`, `BUILDER_DEPOSIT_REQUEST`). Any `StorageChange` recorded in an earlier call at the same `block_access_index` followed by `destroy_storage` in a later call at the same `block_access_index` leaves a stale `StorageChange` in `builder`.
- **Formal Refuter & Patch Proof:** `f_8246_bal_storage_clears_ignored_refuter`, `t_8246_bal_patched_sound`, and `t_8246_bal_tx_block_state_desync` in `Glamsterdam/Eip8246/Spec.lean`.

### 2.2 `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS` (Medium: `EIP-8037` + `EIP-8038` + `EIP-7778` Interaction)
- **Location:** `src/ethereum/forks/amsterdam/vm/instructions/storage.py:120-152` (`sstore`) & `src/ethereum/forks/amsterdam/vm/gas.py:1211-1222` (`settle_transaction_gas`) vs `EIP-7778` (`eip-7778.md:43`)
- **Root Cause:** When a zero storage slot transitions `0 -> X -> 0` within the same transaction (`original_value == 0`):
  1. The first `SSTORE` charges `10,000` execution gas (`STORAGE_WRITE`) and `97,920` state gas (`STORAGE_SET`).
  2. The second `SSTORE` (`X -> 0`) directly restores the `97,920` state gas via `credit_state_gas_refund(evm.gas_meter, StateGasCosts.STORAGE_SET)`, but puts the `10,000` execution gas (`STORAGE_WRITE`) into `evm.gas_meter.refund_counter += int(GasCosts.STORAGE_WRITE)`.
- **Author Defense vs. Arbiter Verdict:**
  - *Author Defense:* `EIP-8037` Intentionally kept execution-gas dirty-reset refunds in `refund_counter` (legacy EIP-2200/3529 mechanism) while only routing state-gas refunds (`97,920`) through `credit_state_gas_refund`.
  - *Arbiter Verdict:* **Confirmed Normative Tension (Medium).** While routing `STORAGE_WRITE` (`10,000`) through `refund_counter` matches EIP-8037's pseudocode, it directly collides with two coupled Glamsterdam changes:
    1. `EIP-7778` (`eip-7778.md:43`) explicitly states: *"Storage discounts that reflect actual reduced computational work (e.g., warm storage access, reverting to original values) remain applied to block gas accounting."* Because `settle_transaction_gas` (`vm/gas.py:1217-1222`) ignores `refund_counter` for block gas, the `10,000` dirty-reset discount is *not* applied to block gas accounting.
    2. Because `credit_state_gas_refund` removed `97,920` from `gas_used_before_refund`, any short transaction (`gas_used_before_refund < 50,000`, e.g., `25,200`) now has `gas_used_before_refund // 5 < 10,000`, clipping up to `4,960` gas of the temporary `STORAGE_WRITE` charge even when the transaction performed zero net state changes.
- **Formal Refuter:** `f_8038_7778_sstore_reset_refuter` in `Glamsterdam/Gas/Spec.lean`.

### 2.3 `F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE` (Low - Defense-in-Depth)
- **Location:** `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:295` (`set_delegation`) & `src/ethereum/forks/amsterdam/state_tracker.py:606-625` (`set_account_balance`)
- **Root Cause & Arbiter Calibration:**
  - All other `StateGasCosts.NEW_ACCOUNT` (`183,600`) charging sites (`call`, `generic_create`, `selfdestruct`, `charge_value_transfer_to_non_alive_account`) check `not is_account_alive(tx_state, addr)`, whereas `set_delegation` (`eoa_delegation.py:295`) checks `if not account_exists(tx_state, authority):`.
  - *Author Defense:* Under canonical post-EIP-161 / EIP-7523 mainnet state (`NoEmptyAccountLeaves`), `PreState` never contains `Some EMPTY_ACCOUNT` (proved in `account_exists_iff_alive_of_no_empty_leaves` in `Glamsterdam/Common/ElCore.lean`), and `create_evm` (`interpreter.py:178`) only checks `get_pre_state_account == EMPTY_ACCOUNT` inside `if tx_env.is_create:`.
  - *Arbiter Verdict:* **Calibrated to Low (Defense-in-Depth).** We proved both the author's invariant (`account_exists_iff_alive_of_no_empty_leaves`) and the exact in-tracker reachability condition (`set_account_balance_zero_creates_empty_leaf` in `ElCore.lean`): unlike `modify_state`, `set_account_balance(tx_state, addr, 0)` (`state_tracker.py:624-625`) calls `set_account` directly without calling `destroy_account`, creating `Some EMPTY_ACCOUNT` in `tx_state.account_writes` (and EEST state tests frequently include explicit empty account leaves in `pre`). Replacing `not account_exists` with `not is_account_alive` at `eoa_delegation.py:295` makes all 5 `NEW_ACCOUNT` charging sites uniform.
- **Formal Refuter:** `f_8037_7702_delegation_exists_vs_alive_refuter` in `Glamsterdam/Gas/Spec.lean`.

### 2.4 `F-8246-UNCHECKED-SYS-TX-DROPS-ACCOUNTS-TO-DELETE` (Low - Defense-in-Depth)
- **Location:** `src/ethereum/forks/amsterdam/fork.py:724-780` (`process_unchecked_system_transaction`) vs `1088-1089` (`process_transaction`)
- **Root Cause & Calibration:** `process_unchecked_system_transaction` calls `process_top_level` and immediately calls `incorporate_tx_into_block(tx_state)` without draining `system_tx_output.accounts_to_delete` via `clear_account_preserving_balance`. While current Amsterdam system contracts (`0x000F...`, `0x00000961...`, `0x0000bbdd...`) do not execute `CREATE` + `SELFDESTRUCT`, adding the 2-line cleanup loop ensures `process_unchecked_system_transaction` preserves the EIP-8246 post-transaction invariant for any future or custom system contract.
- **Formal Refuter:** `f_8246_unchecked_sys_tx_drops_deletes_refuter` in `Glamsterdam/Eip8246/Spec.lean`.

### 2.5 `F-8037-SYS-TX-GAS-LIMIT-INVARIANT` (Low)
- **Location:** `src/ethereum/forks/amsterdam/fork.py:749-755` (`process_unchecked_system_transaction`) vs `src/ethereum/forks/amsterdam/vm/gas.py:1105-1138` (`allocate_evm_gas`)
- **Root Cause & Corrected Citation:** `process_unchecked_system_transaction` (`fork.py:751`) initializes `GasMeter(gas_left=tx_gas_limit, state_gas_left=Uint(0), state_gas_baseline=Uint(0))` with `tx_gas_limit = SYS_TX_GAS_LIMIT = Uint(30_000_000)` (`fork.py:100`), bypassing `allocate_evm_gas` (which caps `execution_gas` at `TX_MAX_GAS_LIMIT = 16,777,216` and places the remaining `13,222,784` in `state_gas_reservoir`).
- **Formal Refuter:** `f_8037_sys_tx_gas_limit_invariant_refuter` in `Glamsterdam/Gas/Spec.lean`.

### 2.6 `F-2780-7928-SET-DELEGATION-OOG-OMITS-RECIPIENT-READ` (Low)
- **Location:** `src/ethereum/forks/amsterdam/vm/interpreter.py:258-277` (`process_top_level`)
- **Root Cause & Corrected Citation:** In `process_top_level` (`interpreter.py:259`), `set_delegation(message)` runs *before* `get_account(tx_state, message.current_target)` (`interpreter.py:277`). When `set_delegation` raises `OutOfGasError` (e.g., when charging `StateGasCosts.NEW_ACCOUNT = 183,600` for an authority), `process_top_level` catches `EthereumException` at line 262, calls `restore_tx_state` and `restore_state_gas_to_entry`, and returns early at line 270 before line 277 is ever reached. Although the sender paid `tx.to`'s `COLD_ACCOUNT_ACCESS` (`3,000` gas) in intrinsic gas (`eip-2780.md:146`), `tx.to` is never added to `tx_state.account_reads` and is omitted from the Block Access List.
- **Formal Refuter:** `f_2780_7928_set_delegation_oog_omits_recipient_refuter` (modeled with `SpecM` in `Glamsterdam/Gas/Spec.lean`).
