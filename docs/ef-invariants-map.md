# EF Glamsterdam Gas Invariants ↔ Verity Closure Map

**Status:** 2026-11-07
**Upstream:** [`ethereum/glamsterdam-gas-invariants`](https://github.com/ethereum/glamsterdam-gas-invariants) (`README.md` + `invariants/inv-1.md` … `inv-8.md`), published with the EF post [“Glamsterdam 8037/8038”](https://blog.ethereum.org/2026/11/06/glamsterdam-8037-8038) on 2026-11-06.
**Pinned spec:** `ethereum/execution-specs@16898000911c1e3caa57be08509536c10ae92d3e` (`Amsterdam D0`), with `EIPs#12581` (`D1/D3/D4/D13/D13R`) and `EIPs#12582` (`D13S/D13A`) variants.

This map exists so each EF invariant can be checked against a Lean declaration instead of a prose claim. Theorem names are the kernel-checked declarations in `Glamsterdam/Gas/CallTree.lean`, `Glamsterdam/Gas/Spec.lean`, `Glamsterdam/Gas/Eip12582.lean`, and `Glamsterdam/Eip8246/Spec.lean`. `audit/guarantees.yaml` is the canonical ledger (60 guarantees at report v3).

## Mapping

| EF invariant | What it protects | Verity theorem(s) | Status | Residual gap |
| :--- | :--- | :--- | :--- | :--- |
| **INV-1** | A failed call does not stop the parent from writing state: with a reservoir, code after a failed call can still write storage and the transaction records the failure. `call{gas:X}` does not bound the callee's state gas. | `t_calltree_e1_fixed_grant_starvation`, `t_calltree_e3_m3_revert_restore_catch_band`, `t_8037_allocate_evm_gas_sound` | Modelled + proved: fixed-grant child starves; parent catch handler is funded by the returned/deferred reservation according to variant. | No client end-to-end trace; the model is EELS-level. |
| **INV-2** | Setting a zero slot and clearing it in the same transaction returns the 97,920 state gas immediately, instead of only at settlement. | `t_calltree_eip12581_same_child_clear_tradeoff`, `t_calltree_d13s_reopens_t2_on_child_clear`, `t_8038_sstore_refund_delta_potential`, `t_8038_refund_counter_telescope_nonneg` | Modelled + proved: `D0` vs `EIPs#12581` trade-off is explicit; `D13S` re-opens the T2 silent-failure band on `1 → 0` clears in helper/`DELEGATECALL` subcalls. | No whole-contract detector; only the gas rule and the adversarial trace. |
| **INV-3** | A reverting call hands back the storage gas it used; a failed `CREATE` hands back 183,600. Callers see more gas left than the old rule predicts. | `t_calltree_e3_m3_revert_restore_catch_band`, `t_calltree_d13s_failed_create_strands_gas`, `t_8037_meter_reservoir_roundtrip_on_revert` | Modelled + proved: `D0/D1/D4` restore revert spill to parent; `D3/D13/D13R/D13S` defer it; failed `CREATE` strands 183,600 in `D13S`. | No client-level `try/catch` corpus. |
| **INV-4** | A fixed gas amount is no longer enough: creating storage/accounts/contracts costs 5–8× more, and updating existing storage costs about 7,200 more per write. | `t_calltree_e1_fixed_grant_starvation`, `t_8038_2780_warm_cold_bounds`, `t_7778_8037_dual_cap` | Partially modelled: the price deltas and the fixed-grant starvation are proved; the contract-level prevalence scan is external. | Whole-contract static impact is not modelled. Use the EF [repricing tool](https://rahul-kothari.github.io/repricing/) for that layer. |
| **INV-5** | `gasleft()` can rise during a call, and reservoir-paid state gas does not appear in it; “gas at start minus gas at end” is no longer the work cost. | `t_12582_prop2_gas_left_non_increasing_in_frame`, `t_calltree_d13r_introduces_new_t1_band`, `t_calltree_d0_preserves_spill_invariant_and_d13s_violates` | Modelled + proved: `D0` preserves the spill invariant; `D13R` introduces a new T1 band; `D13S` violates the invariant. Within-frame monotonicity is proved. | Cross-client `gasleft()` observations are not modelled. |
| **INV-6** | After a call runs out of gas, the retained 1/64 can be enough to finish and record a failure at the new prices. | `t_12582_prop3_subcall_ceiling_bounded`, `t_calltree_e3_m2_dirty_clear_band_and_d13r_break` | Partially modelled: the 63/64 ceiling and the silent-failure band are characterised; the estimator side is a separate gap (below). | `eth_estimateGas` / `eth_call` binary search is not modelled in Lean. |
| **INV-7** | Reserves and stipends sized for today are not enough: the 2,300 stipend of `transfer`/`send` cannot create a storage slot. | `t_calltree_sstore_sentry_excludes_reservoir`, `t_8038_2780_warm_cold_bounds` | Modelled + proved: the SSTORE sentry checks `gas_left` only and excludes the reservoir; the 2,300 stipend cannot create a slot across every fork variant. | Contracts with their own hard-coded reserves still need a client scan. |
| **INV-8** | A 7702 delegation that runs out of gas is rolled back, but its transaction is still mined; anyone can reuse the signed delegation. | `t_8037_7702_delegation_exists_eq_alive_under_invariant`, `f_2780_7928_set_delegation_oog_omits_recipient_refuter` | Partially modelled: the `account_exists` vs `is_account_alive` divergence is proved under the empty-leaf invariant; the OOG ordering in `create_evm` is captured as a refuter. | The replay-after-mined-OOG scenario itself is not yet a theorem. |

## Known gaps (do not over-claim)

1. **Off-chain estimator safety.** The Pimlico report (29 Oct., relayed by Rahul) shows `eth_estimateUserOperationGas` / `eth_call` binary-searching on `gasleft()` deltas can miss reservoir draws above `2^24`. This is a client/RPC-layer property, not an EELS transition property. It needs a standalone estimator lemma (see `docs/war-room-update-2026-11-07.md`, Monday item 2).
2. **INV-8 replay.** The current theorem proves the empty-account/delegation divergence and the OOG ordering refuter, not the full “mined but rolled back, then replay” trace.
3. **INV-4 prevalence.** The Lean model proves the rule; it does not enumerate which deployed contracts break. That remains an external scan with the EF tool.
4. **Client differential.** `make check` covers the pinned EELS/Python model and the C-ABI differential. Geth/Reth/Nethermind behaviour is outside this repo.

## Reproduce

```bash
make check                 # Lean build + turbo-lean gates + differential + metadata
python3 scripts/verify_ground_truth.py --self-test
python3 scripts/verify_ground_truth.py --enforce-ledger-step all
```

The external tracker for ecosystem findings is [`ethereum/8037-findings`](https://github.com/ethereum/8037-findings); the consolidated external count at 2026-11-07 is roughly **6 HIGH / 66 MEDIUM / 51+ LOW** (EF + Dedaub + ChainSecurity), which is a different unit from this repo's 60 kernel-checked guarantees.
