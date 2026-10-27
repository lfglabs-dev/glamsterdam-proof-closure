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
4. Track two verifier issues separately: untrusted native-thread/`RLIMIT_DATA` failures, and cached receipts losing sandbox status. Francesco owns theorem restatements restoring the pinned allowlist bytes; avoid a competing server deployment while that proceeds. Do not claim remote verification while it returns 422.
5. Keep this private repository synchronized with jo/main receipts, source pins, findings, assumptions, and Hindsight context.

## Source and freshness notes

- Verified upstream jo: `fc0343e` (PR #99 merged); latest observed R1 branch: `parithosh/r1-static-call` at `42b6d0b`.
- Private repo baseline before this update: `377f71c`.
- Signal/Hindsight refresh is pending Orb approval for `SPARK_MEMORY_API_TOKEN` (request `fd78d519-27a2-49be-a819-b2e554ae9276`). No Signal content is presented here as freshly queried until that approval succeeds; the coordination facts above come from verified repo/issue records.

## Coordination refresh — 2026-10-27 07:22 UTC

- Francesco retained the overnight delegated merges, including #99. Main merges and statement changes again require his approval; green jo self-merges remain authorized.
- #102 merged at `a84d5ae`: concrete witnesses for the four J `_reach` supporting theorems, without changing the 146/142/4 board counts.
- #100 (R1) and #101 (R2/R3) await lead decisions; do not describe their fixes as landed. #103 adds the missing EXTCODE* warm-before-OOG regressions and belongs to Parithosh.
- CallBridge remains Osaka CALL first. CREATE/codeMap, precompiles and Amsterdam are later scope. Parithosh owns CallBridge, the S2 equivalence lemma and R5 source correction; Kev owns J01 address binding, J03 outcome/gas/effects correspondence, and a protected-slot J05 witness.
- New F03 rows-union-pruned coverage obligation would increase 49 obligations to 50; approved in principle only, exact statement change still subject to review.
- Distinguish (C) from C′: (C) CLEAN verdicts remain void pending its soundness fix. C′ results using fixed checker `067bca3` count **modulo completeness and the adversarial corpus**. C′ NOT CLEAN without EELS replay is a candidate, not a finding.
- Our assigned verifier work is the native-thread/RLIMIT_DATA failure and cached sandbox-status loss. The lead is restoring the old allowlist bytes by restating three theorems; Option A is not deployed and should not duplicate that immediate remediation.

Sources: [lead decisions](https://github.com/fradamt/8037-coordination/issues/191#issuecomment-6436035015), [ownership](https://github.com/fradamt/8037-coordination/issues/191#issuecomment-6436079531), [J witness merge](https://github.com/fradamt/8037-coordination/issues/191#issuecomment-6436149381).

## Validation of this private documentation update

`make prove` passes (12 jobs; 60 guarantees/61 source mappings; kernel axiom audit 60/60).
The full `make check` attempt stopped at `turbo-verify`: installed Turbo-Lean rejected
`defaultFacets := #[LeanLib.staticFacet]` for `glamsterdam_spec_cabi` in `lakefile.lean`.
It did **not** reach the differential-test stage. The earlier PR #1 comment attributing
this failure to missing differential dependencies was incorrect. No new Lean guarantee,
source-map pin, or full-audit closure is asserted by this documentation update.
Signal/Hindsight remains pending the same access request; this is repository-sourced context.

### Validation refresh — 2026-10-27 08:31 UTC

Turbo-Lean PR #262 merged as `b862fbf`; independent Astra review found no blocker.
A release binary built from its identical source tree `cd3cc3f` has SHA-256
`372c155fba8316d82c8f7c1ba56268947f0af14e2c8d4f2e677ba6f7d6374389`.
With this binary and Lean 4.31, trusted ci-verify passes: 17 files, 336 theorem
shards, zero sorry/native_decide; receipt
`1728eb19bb35b29f9da89a26f8f359455a189fbca5e77c09461b7b7324db4add`.

The first corrected run then exposed missing generated C for MetaSpec in the
differential shared library. `lake build glamsterdam_spec_cabi` supplied the
missing artifacts (23 jobs). After that explicit preparation, `make check`
passed: all seven pytest cases, differential agreement, 60/60 kernel axiom
audit, 23 vendored hashes and 61 source mappings. Its trusted verifier reused
the preceding successful receipt. This is not an untrusted Warci result or a
claim that unprepared `make check` builds every required C artifact.

Upstream `main` at `596ed68` restores the server-pinned allowlist, per the lead's
[confirmation](https://github.com/fradamt/8037-coordination/issues/191#issuecomment-6436669470).
Fetched jo `95db803` still has hash `1752669a…`, so it still needs that main
integration. No server re-pin is needed. CallBridge/J work remains with its
owners; cached sandbox provenance and native-thread/RLIMIT reproduction remain
our separate open verifier issues. No fresh Signal information was accessed.
