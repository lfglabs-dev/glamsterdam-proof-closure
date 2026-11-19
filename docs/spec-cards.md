# Glamsterdam Spec Cards — 12 statements an auditor can check

**Status:** draft, 2026-11-07
**Pinned spec:** `ethereum/execution-specs@16898000911c1e3caa57be08509536c10ae92d3e` (`Amsterdam D0`), variants `EIPs#12581` / `#12582`
**Rule:** every card is one statement, one source range, one positive witness, one mutant. If a card needs two independent claims, split it. If it is not yet proved, say `GAP` instead of hiding it.

Read in this order: **Card 1 → Card 3 → Card 2 → Card 4 → Card 7 → Card 5 → Card 6 → Card 8 → Cards 9–12**. Cards 1–3 are the core silent-failure mechanism; the rest are consequences and adjacent audits.

## Card 1 — INV-1: a failed child does not bound the parent’s next write

- **Claim.** If a child call exhausts its execution gas and fails, the parent can still execute a storage write on the failure path; the child’s `gas` argument does not bound the state gas that write consumes. The reservoir, not the child grant, funds it.
- **Lean signature (target).**
  ```lean
  theorem inv1_failed_call_parent_write
    (f : ForkParams) (m : GasMeter) (grant : Nat)
    (hgrant : grant ≤ m.gasLeft)
    (hfail  : execChild f m grant = .outOfGas) :
    ∃ m1 m2, exitChild f m grant = .some m1 ∧
             m1.gasLeft < 110_020 ∧
             m1.stateGasLeft ≥ 97_920 ∧
             stepParentWrite f m1 = .ok m2
  ```
- **Source.** `vm/gas.py:379–616`, `vm/instructions/storage.py:68–162`; `Glamsterdam/Gas/CallTree.lean`.
- **Witness.** `t_calltree_e3_m3_revert_restore_catch_band` (revert path) and `t_calltree_e1_fixed_grant_starvation` (fixed grant).
- **Mutant.** Remove `repay_state_gas_spill` / `restore_state_gas` from the child exit; the parent write must then OOG.
- **Assumptions.** 63/64 cap; stipend rules; EELS state journal.
- **Reviewer checklist.** Does the theorem quantify over the parent write, not just the child exit? Is the reservoir explicitly in the conclusion? Is the D0/D1/D3/D4/D13/D13R/D13S choice a parameter, not a duplicated proof?

## Card 2 — INV-2: same-transaction `0 → x → 0` returns 97,920 immediately

- **Claim.** Setting a zero slot and clearing it in the same transaction returns the 97,920 state gas at the clear, not only at settlement. A lock/flag set and reset around an external call is the classic broken pattern.
- **Lean signature (target).**
  ```lean
  theorem inv2_same_tx_clear_returns_state_gas
    (f : ForkParams) (m : GasMeter) (k : Address) :
    let m1 := sstore f m k 0 1
    let m2 := sstore f m1 k 1 0
    m2.gasLeft + m2.stateGasLeft = m.gasLeft + m.stateGasLeft + 97_920
  ```
- **Source.** `vm/instructions/storage.py:126–139`; `Glamsterdam/Gas/Spec.lean`, `CallTree.lean`.
- **Witness.** `t_8038_sstore_refund_delta_potential`, `t_8038_refund_counter_telescope_nonneg`, `t_calltree_eip12581_same_child_clear_tradeoff`.
- **Mutant.** Use the Osaka refund rule (refund only at settlement); the equation must fail.
- **Assumptions.** `orig = 0`, `curr = 0`; no intervening write; same frame or helper call as stated.
- **Reviewer checklist.** Is the 97,920 constant tied to the source table? Does the theorem distinguish same-frame from helper/`DELEGATECALL` clear (the `D13S` T2 band)?

## Card 3 — INV-3: revert and failed `CREATE` hand back storage gas

- **Claim.** A reverting child returns the storage gas it drew; a failed `CREATE` returns 183,600. The parent sees more gas than the old “revert burns everything” rule predicts.
- **Lean signature (target).**
  ```lean
  theorem inv3_revert_returns_state_gas
    (f : ForkParams) (m : GasMeter) (grant : Nat) :
    (execChild f m grant = .reverted) →
    ∃ m', m'.stateGasSpilled = m.stateGasSpilled ∧ m'.gasLeft ≥ m.gasLeft
  ```
- **Source.** `vm/gas.py:379–616`, `vm/instructions/system.py:59–186`; `CallTree.lean`.
- **Witness.** `t_calltree_e3_m3_revert_restore_catch_band`, `t_calltree_d13s_failed_create_strands_gas`.
- **Mutant.** Skip `restore_state_gas` on revert; the parent catch path must OOG.
- **Assumptions.** The child actually drew state gas; the revert carries no state changes.
- **Reviewer checklist.** Does the theorem cover both `REVERT` and failed `CREATE`? Is the `D13S` stranded-183,600 case explicit?

## Card 4 — INV-4: fixed gas budgets are no longer enough

- **Claim.** New storage, new accounts, and contract creation cost 5–8× more; updating existing storage costs about 7,200 more per write. A fixed budget (hard-coded in a contract, relayer, or signed message) can be insufficient even when it was sufficient on Osaka.
- **Lean signature (target).**
  ```lean
  theorem inv4_fixed_budget_starvation
    (b : Nat) (h : b = 50_000) :
    ∃ trace, costAmsterdam trace > b ∧ costOsaka trace ≤ b
  ```
- **Source.** EF gas table; `Glamsterdam/Gas/Spec.lean`, `CallTree.lean`.
- **Witness.** `t_calltree_e1_fixed_grant_starvation` (50,000 grant, fresh slot), `t_8038_2780_warm_cold_bounds`, `t_7778_8037_dual_cap`.
- **Mutant.** Restore Osaka prices; the witness must disappear.
- **Assumptions.** The trace is a single fresh `SSTORE` in a fixed-grant child; no refund intervenes.
- **Reviewer checklist.** Are the numbers quoted from the EF table, not from memory? Is the statement about a family of budgets, not one arbitrary constant?

## Card 5 — INV-5: `gasleft()` can rise; reservoir gas is invisible

- **Claim.** Within a frame `gasleft()` is non-increasing, but across a child exit it can rise, and reservoir-paid state gas does not appear in `gasleft()` at all. Billing by `gasStart - gasEnd` is unsound.
- **Lean signature (target).**
  ```lean
  theorem inv5_cross_frame_gasleft_rise
    (f : ForkParams) (m : GasMeter) (grant : Nat) :
    execChild f m grant = .ok m' →
    m'.gasLeft ≥ m.gasLeft ∨ m'.stateGasSpilled > m.stateGasSpilled
  ```
- **Source.** `vm/gas.py:379–616`; `Glamsterdam/Gas/Eip12582.lean`, `CallTree.lean`.
- **Witness.** `t_12582_prop2_gas_left_non_increasing_in_frame` (within-frame), `t_calltree_d13r_introduces_new_t1_band` (cross-frame rise), `t_calltree_d0_preserves_spill_invariant_and_d13s_violates`.
- **Mutant.** Assume `gasleft()` is globally monotone; the D13R witness must fail.
- **Assumptions.** The child exit path is one of the seven variants; the reservoir exists only when `tx.gas > 2^24`.
- **Reviewer checklist.** Does the card state both the within-frame theorem and the cross-frame counterexample? Is the reservoir condition explicit?

## Card 6 — INV-6: the retained 1/64 can be enough to finish

- **Claim.** After a call OOGs, the retained 1/64 can be enough to finish and record a failure at Amsterdam prices. Gas estimates can land in this band.
- **Lean signature (target).**
  ```lean
  theorem inv6_retained_64th_can_finish
    (f : ForkParams) (m : GasMeter) (grant : Nat)
    (h : execChild f m grant = .outOfGas) :
    ∃ m1, exitChild f m grant = .some m1 ∧
          m1.gasLeft ≤ m.gasLeft / 64 ∧
          m1.gasLeft ≥ 12_100
  ```
- **Source.** `vm/gas.py:379–616`; `Glamsterdam/Gas/Eip12582.lean`, `CallTree.lean`.
- **Witness.** `t_12582_prop3_subcall_ceiling_bounded`, `t_calltree_e3_m2_dirty_clear_band_and_d13r_break`.
- **Mutant.** Assume retained gas is below the failure-record cost; the band witness must fail.
- **Assumptions.** The failure path writes one slot; the 1/64 is computed under the pinned rule.
- **Reviewer checklist.** Is the cost of the failure path explicit? Is the band tied to a concrete trace?

## Card 7 — INV-7: the 2,300 stipend cannot create a slot

- **Claim.** `transfer`/`send` forward 2,300 gas; a callee that writes a fresh storage slot cannot succeed. The SSTORE sentry checks `gas_left` only and deliberately excludes the reservoir.
- **Lean signature (target).**
  ```lean
  theorem inv7_stipend_cannot_create_slot
    (f : ForkParams) (m : GasMeter) :
    m.gasLeft = 2_300 → sstore f m k 0 1 = .outOfGas
  ```
- **Source.** `vm/instructions/storage.py:100–105`, `vm/gas.py:84`; `CallTree.lean`.
- **Witness.** `t_calltree_sstore_sentry_excludes_reservoir`, `t_8038_2780_warm_cold_bounds`.
- **Mutant.** Let the sentry see `state_gas_left`; the theorem must fail.
- **Assumptions.** `CALL_STIPEND = 2,300`; the slot is fresh; no prior reservoir draw.
- **Reviewer checklist.** Does the theorem mention both `gas_left` and the reservoir exclusion? Is the constant pinned?

## Card 8 — INV-8: `0 → x → 0` can make `gasleft()` rise (billing hazard)

- **Claim.** A `0 → x → 0` sequence can increase `gasleft()` at a subcall boundary. Contracts that charge by `gasleft()` deltas must clamp and cap the measurement.
- **Lean signature (target).**
  ```lean
  theorem inv8_gasleft_delta_not_cost
    (f : ForkParams) (m : GasMeter) (k : Address) :
    let m1 := sstore f m k 0 1
    let m2 := sstore f m1 k 1 0
    m2.gasLeft > m1.gasLeft
  ```
- **Source.** `vm/instructions/storage.py:126–139`; `Glamsterdam/Gas/CallTree.lean`.
- **Witness.** `t_calltree_d13s_reopens_t2_on_child_clear`, `t_calltree_eip12581_same_child_clear_tradeoff`.
- **Mutant.** Assume `gasleft()` is non-increasing across the clear; the witness must fail.
- **Assumptions.** The clear happens in a helper/`DELEGATECALL` subcall for the D13S band; same-frame for the simple form.
- **Reviewer checklist.** Is this card kept separate from the 7702 replay card (Card 12)? Are the two hazards not conflated?

## Card 9 — EIP-8246 cleanup

Use the execution-layer declarations below. Transaction-state cleanup, fee accounting and per-slot BAL replay each have a different observable result.

## Card 10 — EIP-7732 settlement

Use the consensus declarations below. Bid coverage is a precondition of the supply theorem. The lifecycle theorems count withdrawals queued for one bid.

## Card 11 — EIP-8282 requests at the consensus boundary

An empty parent requires empty requests. A full parent requires the requests root committed in the bid. The separate contract audit owns evidence about FIFO ordering inside the EIP-8282 contract.

## Card 12 — EIP-7702: delegation OOG and replay

- **Claim.** If a 7702 delegation runs out of gas, the delegation is rolled back but the transaction is mined; the signed authorization can be replayed. A `setup`/`initialize` guarded only by “the tx was mined” is unsafe.
- **Lean signature (target).**
  ```lean
  theorem eip7702_replay_after_mined_oog
    (s : PreState) (auth : Authorization) :
    mined (executeAuth s auth) ∧ rolledBack (executeAuth s auth) →
    ∃ s', executeAuth s' auth = .ok ∧ s'.delegation = auth.target
  ```
- **Status.** `GAP` — `t_8037_7702_delegation_exists_eq_alive_under_invariant` proves the `account_exists` vs `is_account_alive` divergence, and `f_2780_7928_set_delegation_oog_omits_recipient_refuter` captures the OOG ordering, but the full replay trace is not yet a theorem.
- **Source.** `vm/eoa_delegation.py:295`, `vm/instructions/system.py`; `Glamsterdam/Gas/Spec.lean`.
- **Witness.** `f_2780_7928_set_delegation_oog_omits_recipient_refuter`.
- **Mutant.** Assume mined ⇒ delegation applied; the OOG witness must fail.
- **Reviewer checklist.** Is the card explicitly marked `GAP`? Is the replay assumption stated, not hidden?

## What is not in the trusted base

- `MetaSpec` combinators, `WitnessRefuter` machinery, and the audit linter stay in `audit/tools/`; they are review tooling, not proof assumptions.
- The seven fork variants collapse into `ForkParams`; only the fields that change `D0` vs `D13S` behaviour are trusted.
- Client-level behaviour (geth/reth/nethermind), RPC estimators, and deployed-contract prevalence are outside these cards and must be cited as external evidence, not as Lean guarantees.

## Proof destinations for the internal notes

The reviewed notes are pinned at `11649a0`. The consensus reference is Gloas `aa16bb4c` and the execution reference is Amsterdam `16898000`. The [source map](../audit/source-map.yaml) identifies upstream symbols and distinguishes translations from projections. Each link below opens the declaration at this revision.

### Consensus

| Observable result and scope | Declaration or test |
| --- | --- |
| One covered bid conserves the modeled builder debit plus queued amount. | [t_7732_no_eth_minting](../Glamsterdam/Gloas7732/Spec.lean#L331) |
| Positive quorum, one slot, four confirmation timings. Bound both the amount and the number of entries. | [t_7732_single_settlement](../Glamsterdam/Gloas7732/Spec.lean#L228) · [t_7732_single_withdrawal_entry](../Glamsterdam/Gloas7732/Spec.lean#L247) |
| A positive confirmed or quorum-qualified bid queues its exact amount for the bid’s fee recipient. The balance check covers existing obligations and this bid at admission. | [t_7732_payment_guarantee](../Glamsterdam/Gloas7732/Spec.lean#L263) · [t_7732_builder_solvency](../Glamsterdam/Gloas7732/Spec.lean#L305) · [t_7732_builder_withdrawal_no_underflow](../Glamsterdam/Gloas7732/Spec.lean#L319) |
| Repeated participation by a validator within the modeled epoch contributes at most one effective balance. | [t_7732_quorum_weight_unconditional](../Glamsterdam/Gloas7732/Spec.lean#L419) · [t_7732_quorum_no_double_count](../Glamsterdam/Gloas7732/Spec.lean#L402) |
| Three projected roots survive parent-payment processing. Exit initiation requires zero pending amount. | [t_7732_pinned_payment_frame](../Glamsterdam/Gloas7732/Spec.lean#L666) · [t_7732_frame](../Glamsterdam/Gloas7732/Spec.lean#L658) · [t_7732_exit_safety](../Glamsterdam/Gloas7732/Spec.lean#L363) |
| A competing same-slot payload cannot pass the commitment under the stated hash uniqueness hypothesis. Network visibility and fork choice are outside the transition. | [t_7732_same_slot_unbundling](../Glamsterdam/Gloas7732/Spec.lean#L468) |
| Issue #5754. Compare the beta.4 witness and composed trace with the proposed transition’s queue equality. | [f_7732_slashed_payment_resurrection_refuter](../Glamsterdam/Gloas7732/Spec.lean#L572) · [t_7732_composed_trace_resurrects_slashed_payment](../Glamsterdam/Gloas7732/Spec.lean#L629) · [t_7732_slashed_no_resurrection](../Glamsterdam/Gloas7732/Spec.lean#L561) · [test_vendored_gloas_slashed_payment_resurrection_trace](../tests/differential/test_glamsterdam_differential.py#L588) |
| Fork-slot initialization, ring index aliasing, and the two credential checks each have a concrete witness. | [f_7732_fork_slot_availability_refuter](../Glamsterdam/Gloas7732/Spec.lean#L855) · [f_7732_availability_ring_buffer_clobber_refuter](../Glamsterdam/Gloas7732/Spec.lean#L897) · [t_7732_mainnet_ring_alias](../Glamsterdam/Gloas7732/Spec.lean#L912) · [f_8282_topup_credential_prefix_drop_refuter](../Glamsterdam/Gloas7732/Spec.lean#L737) · [f_7732_fork_onboard_cross_credential_refuter](../Glamsterdam/Gloas7732/Spec.lean#L781) |
| Consensus acceptance of parent execution requests. | [t_8282_7732_queue_safety](../Glamsterdam/Gloas7732/Spec.lean#L688) |

### Execution gas

| Observable result and scope | Declaration or test |
| --- | --- |
| Charges and reservoir return on success, error and revert. | [t_8037_charge_gas_sound](../Glamsterdam/Gas/Spec.lean#L76) · [t_8037_reservoir_roundtrip_success](../Glamsterdam/Gas/Spec.lean#L92) · [t_8037_reservoir_roundtrip_error](../Glamsterdam/Gas/Spec.lean#L96) · [t_8037_meter_reservoir_roundtrip_on_revert](../Glamsterdam/Gas/Spec.lean#L106) |
| Valid intrinsic costs, transaction allocation, system reservoir, block caps and access prices. | [t_8037_allocate_evm_gas_sound](../Glamsterdam/Gas/Spec.lean#L307) · [t_8037_sys_tx_reservoir_sound](../Glamsterdam/Gas/Spec.lean#L670) · [t_7778_8037_dual_cap](../Glamsterdam/Gas/Spec.lean#L359) · [t_8038_2780_warm_cold_bounds](../Glamsterdam/Gas/Spec.lean#L369) |
| Root non-negativity on an abstract storage trace and a reset/refill witness. | [t_8038_refund_counter_telescope_trace_root_nonneg](../Glamsterdam/Gas/Spec.lean#L594) · [f_8038_7778_sstore_reset_refuter](../Glamsterdam/Gas/Spec.lean#L468) |
| 50,000 granted gas and zero reservoir. D13 represents the #12581 refill behavior. #12582 enters the frame successfully. The same warm fresh-slot write succeeds when the reservoir is funded. | [t_calltree_e1_fixed_grant_starvation](../Glamsterdam/Gas/CallTree.lean#L332) · [t_calltree_d13_eq_eip12581_on_gas_and_reservoir](../Glamsterdam/Gas/CallTree.lean#L850) · [t_12582_fixed_budget_empty_reservoir](../Glamsterdam/Gas/Eip12582.lean#L819) |
| #12582 library equality assumes successful execution, identical meter operations and full forwarding after call cost. The draw bound applies to non-inheriting calls. | [t_12582_prop1_delegatecall_frame_invariance](../Glamsterdam/Gas/Eip12582.lean#L430) · [t_12582_prop2_gas_left_non_increasing_in_frame](../Glamsterdam/Gas/Eip12582.lean#L543) · [t_12582_prop3b_untrusted_callee_reservoir_drain_bound](../Glamsterdam/Gas/Eip12582.lean#L726) · [t_12582_prop4_revert_vs_refill_drawn_asymmetry](../Glamsterdam/Gas/Eip12582.lean#L847) |
| D13S sibling delta, helper failure and stranded CREATE gas are three different observations. | [t_calltree_e3_m4_sibling_underflow_and_d13s_break](../Glamsterdam/Gas/CallTree.lean#L591) · [t_calltree_d13s_reopens_t2_on_child_clear](../Glamsterdam/Gas/CallTree.lean#L647) · [t_calltree_d13s_failed_create_strands_gas](../Glamsterdam/Gas/CallTree.lean#L719) |
| Abstract estimator and the 500k/16.9M comparison. | [estimator_unsound_above_2pow24](../Glamsterdam/Gas/Spec.lean#L840) · [estimator_unsound_above_2pow24_witness](../Glamsterdam/Gas/Spec.lean#L903) · [t_8037_c13_fixed_budget_subcall_tx_gas_dependent](../Glamsterdam/Gas/Spec.lean#L967) |
| Prototype proxy comparison uses a modeled allowance rule. A current client run requires independent evidence. | [t_12582_prop1b_nethermind15187_proxied_factory_divergence](../Glamsterdam/Gas/Eip12582.lean#L531) |
| Delegation OOG before recipient lookup and the empty-account distinction. | [f_2780_7928_set_delegation_oog_omits_recipient_refuter](../Glamsterdam/Gas/Spec.lean#L742) · [t_8037_7702_delegation_exists_eq_alive_under_invariant](../Glamsterdam/Gas/Spec.lean#L619) · [f_8037_7702_delegation_exists_vs_alive_refuter](../Glamsterdam/Gas/Spec.lean#L631) |

### SELFDESTRUCT and the block access list

| Observable result and scope | Declaration or test |
| --- | --- |
| Local transfers, rollback, SELFDESTRUCT, cleanup and fee accounting. Their composition across arbitrary bytecode is outside these declarations. | [move_ether_distinct_conserves_sum](../Glamsterdam/Common/ElCore.lean#L632) · [t_common_checkpoint_rollback](../Glamsterdam/Common/ElCore.lean#L616) · [t_8246_selfdestruct_conservation](../Glamsterdam/Eip8246/Spec.lean#L129) · [t_8246_eth_conservation](../Glamsterdam/Eip8246/Spec.lean#L283) · [t_8246_tx_fee_settlement_conservation](../Glamsterdam/Eip8246/Spec.lean#L260) |
| Cleanup preserves balance, clears code/nonce/storage and passes the creation collision check. Successful initcode execution is a separate question. | [t_8246_tx_state_clear_exact](../Glamsterdam/Eip8246/Spec.lean#L57) · [t_8246_cleared_address_deployable](../Glamsterdam/Eip8246/Spec.lean#L75) · [t_8246_no_state_gas_refund](../Glamsterdam/Eip8246/Spec.lean#L181) |
| The pinned write/clear trace diverges. Patched storage replay is proved at the modeled address/slot. | [t_8246_bal_tx_block_state_desync](../Glamsterdam/Eip8246/Spec.lean#L424) · [f_8246_bal_storage_clears_ignored_refuter](../Glamsterdam/Eip8246/Spec.lean#L393) · [t_8246_bal_patched_sound](../Glamsterdam/Eip8246/Spec.lean#L364) · [t_8246_storage_clears_recorded_in_bal](../Glamsterdam/Eip8246/Spec.lean#L462) |
| Unchecked system-transaction cleanup omission in the modeled projection. | [f_8246_unchecked_sys_tx_drops_deletes_refuter](../Glamsterdam/Eip8246/Spec.lean#L511) |

### Conformance evidence

The [differential suite](../tests/differential/test_glamsterdam_differential.py) runs selected fixed and generated cases through the C ABI. The [pinned reference files](../audit/source-map.yaml) identify the source being compared. The suite does not enumerate an official EF vector release, count its expected cases, or reconcile skips. Its pass count establishes coverage of the cases actually exercised.
