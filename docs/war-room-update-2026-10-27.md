# Glamsterdam war-room update — 2026-10-27

## Current direction

The project is moving from isolated theorem closure toward a pinned, executable audit record: upstream EELS/EIP/consensus sources remain hash-pinned; Lean statements and proofs are checked by `lake`, `premerge`, `turbo-lean`, and metadata ledgers; concrete witnesses and mutation controls are required before a guarantee is treated as useful.

The EL gas track is now connected to the completeness work in `fradamt/evm-gas-semantics-lean`. Its jo line has merged the G04/GTree/JUMPI/fault and witness waves, CallBridge part 1, AddressCodec/CALLCODE probes, and the concrete GAS identity witness from PR #99 (`fc0343e`). The current jo board is 146 theorems, 142 witnessed, 4 allow-listed. The remaining four are CallBridge-dependent and owned by the upstream teams.

## What was hard

- The coupled execution/state-gas model has reservoir, spill, refund, and child-frame restoration interactions. Naive rollback accounting can underflow signed spill or bypass the EIP-12582 ceiling.
- Statement fidelity matters as much as proof completion. Counterexamples exposed CALL warm-order, Osaka static-CALL grant, CALLCODE journal, settlement-ledger, and `.finished` phase mismatches between Exec and the source model.
- Completeness proofs needed concrete witnesses, not only theorem declarations. The board moved from statement-only obligations to a small set of witnessed, audited rows.
- The Warci protected-file hash is stale relative to `main`/jo's four-entry allowlist. Remote checks therefore return 422 even when local gates pass.
- The clean-check coverage pilot is provisional: no CLEAN verdict counts until the soundness fix on `codex/enum-coverage` lands.

## What was studied

- EELS Amsterdam gas accounting: `charge_gas`, state-gas reservoir/refill, 63/64 grants, SSTORE sentry, refunds, system transactions, warm/cold access, and CALL/CREATE settlement.
- EIP-12582 delayed rollback credit and the `drawn` versus `state_gas_rolled_back` invariant.
- EIP-8246 account clearing and SELFDESTRUCT balance/storage conservation.
- EIP-7732/8282 payment, queue, solvency, slashing, and deferred-execution properties.
- Completeness enumeration: B/Q/V/G/J/O/F witnesses, canonical CallBridge reachability, and negative controls for malformed identity rows.

## What remains

1. Complete the four CallBridge-dependent board entries (`O02_source_canonical`, `J03_call_prepared_canonical`, `J03_of_call_family_canonical`, `O05_of_J04`).
2. Land and gate the Osaka static-CALL grant fix (R1), then the R2/R3 settlement and phase fixes, with before/after kernel regressions.
3. Finish the `codex/enum-coverage` soundness fix before treating CLEAN coverage results as evidence.
4. Repair Warci's allowlist trust path: deploy the reviewed `origin/main` auto-trust policy or restore the pinned allowlist bytes; do not claim remote verification while it returns 422.
5. Keep this private repository synchronized with jo/main receipts, source pins, findings, assumptions, and Hindsight context.

## Source and freshness notes

- Verified upstream jo: `fc0343e` (PR #99 merged); latest observed R1 branch: `parithosh/r1-static-call` at `42b6d0b`.
- Private repo baseline before this update: `377f71c`.
- Signal/Hindsight refresh is pending Orb approval for `SPARK_MEMORY_API_TOKEN` (request `fd78d519-27a2-49be-a819-b2e554ae9276`). No Signal content is presented here as freshly queried until that approval succeeds; the coordination facts above come from verified repo/issue records.
