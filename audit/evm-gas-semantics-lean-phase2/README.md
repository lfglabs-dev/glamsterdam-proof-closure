# Phase 2 Proof Closure Artifacts (`fradamt/evm-gas-semantics-lean`)

This directory archives the Phase-2 Lean 4.35.0 proof artifacts developed and verified with `turbo-lean` (Zero-Trust Oracle + `audit-spec`) for `fradamt/evm-gas-semantics-lean`:

- **`NeedExact.lean`**: Complete zero-`sorry`, zero-warning proofs of the 7 remaining non-optional DESIGN §6 skeleton leaves on top of `origin/main`:
  - `S13` (`success_monotone`)
  - `S15` (`runsAsDescribed_monotone`)
  - `S21` (`need_exact`)
  - `S22` (`need_exact_runsAsDescribed`)
  - `S23` (`need_exact_of_clean_trace`)
  - `S24` (`bisectEstimate_eq_need`)
  - `S25` (`bisectEstimate_eq_need_of_clean_trace`)
  Together with the 29 leaves on `fradamt/evm-gas-semantics-lean` `main`, this brings `leafcheck.py` to **36/37 DESIGN §6 skeleton leaves proved (`statement diffs 0`)**, leaving only the optional conjecture `S27` (`outcome_bands_length_le_optional_weakest`).
- **`SimMeter.lean`**, **`SimWorld.lean`**, **`SimBasicStep.lean`**, **`SimCallCreate.lean`**, **`AmsterdamDimensions.lean`**, **`AvoidNestedOOG.lean`**: Maxwell Wave-1/2/3 simulation and usage-invariance proof modules.
