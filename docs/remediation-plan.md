# Remediation and Improvement Plan — Glamsterdam gas audit

**Status:** proposed, 2026-11-07
**Scope:** the 60 formal guarantees, the 10 verified edge-case findings, and the EF 8-invariant surface (`INV-1…8`), plus the adjacent 8246 / ePBS / 8282 / 7702 audits.
**Goal:** make the proof surface small enough to audit in a day, close the two real gaps, and turn the audit into address-level evidence EF can act on.

## 0. What “done” means

| Outcome | Acceptance test |
|---|---|
| Trusted core is small | `SpecCore/` ≤ ~600 LoC; one state type; five meter transitions; two stack transitions; no duplicated per-fork lemmas |
| Cards are auditable | 12 cards, each ≤30 lines, one statement, one source range, one witness, one mutant; mutant test fails when the mechanism is removed |
| Refinement is explicit | `specCore_refines_eels` stated; either proved or marked as the single open obligation |
| Gaps are honest | 7702 replay and estimator safety are either proved or labelled `GAP` with a concrete witness |
| Evidence is real | ≥20 address-level rows pass the evidence gate, or the report says “none found” with the search method |
| EF can act | One-page report + 12-card appendix delivered to `glamsterdam@ethereum.org`; no public 0-day disclosure |
| Build stays green | `make check` passes; `0 sorryAx`, `0 native_decide`, `0 trustCompiler` |

## 1. Workstreams

### WS1 — Trusted core (`SpecCore/`)

**Problem:** four overlapping meters (`EvmGasFrame`, `GasMeter`, `CallFrameMeter`, `D13AMeter`) and an 8-way `ForkSchedule × AllowanceMode` product mean the same fact is proved several times. A reviewer cannot tell which copy is trusted.

**Plan.**
1. Add `ForkParams` as the only fork-dependent record: `refill` (`LIFO | ReservoirOnly`), `revertSpill` (`Restore | Defer`), `allowance` (`Unlimited | PerFrame12582`), plus `reservoirThreshold = 2^24`. D0/D13R/D13A become three values, not three proof families.
2. Add `MeterCore.lean` with exactly five transitions: `allocate_tx_gas`, `charge_exec`, `charge_state`, `credit_state_refund`, `settle_tx_gas`.
3. Add `CallStack.lean` with exactly two transitions: `pushFrame` (63/64 cap, reservoir forward, `DELEGATECALL` ceiling inheritance vs `CALL`/`CREATE` cap) and `popFrame` (success / revert / halt, 7702 entry rollback).
4. Keep every existing theorem as a corollary during migration; do not rename or delete C-ABI symbols.
5. Delete `D13AMeter` and the duplicated per-variant lemmas only after `Refine.lean` is green.

**Acceptance:** the five meter transitions and two stack transitions are the only definitions in the trusted path; the old modules are projections.

### WS2 — Twelve cards, one statement each

**Problem:** several claims are conjunctions of unrelated facts; some are vacuous without a mutant; fork-dependent truth values were unlabelled.

**Plan.**
1. Freeze card IDs C1–C12 and the `fork_variant ∈ {D0, D13R, D13A}` field in every claim.
2. For each card, write: claim, Lean signature, source range, positive witness, mutant, assumptions, reviewer checklist.
3. Add a `mutant` test for each card: remove the refund / restore / cap / reservoir condition and confirm the theorem fails.
4. Split any card that needs two independent facts. Current candidates to watch: C1 (parent write vs reservoir accounting), C8 (same-frame vs helper clear), C12 (delegation rollback vs replay).
5. Publish `docs/README-spec-review.md` as the 20-minute path; C1 → C3 → C2 → C4 first.

**Acceptance:** every card has a failing mutant; no card cites two theorems for one claim; no card is true only under an unstated client assumption.

### WS3 — Close the two real gaps

**Gap A — 7702 replay after mined OOG.**
- Formalize the trace: authorization processing OOG → delegation and nonce bump rolled back → sender nonce advances → signed tuple remains valid → attacker includes it in a new type-4 tx → `initialize(attacker)` succeeds.
- Required lemmas: authorization validity after rollback, nonce monotonicity, replay composition.
- Until proved, C12 stays `GAP`; do not present it as a guarantee.

**Gap B — estimator safety above `2^24`.**
- Build the minimal witness in `docs/estimator-safety-spec.md`.
- Model `EstimatorSafety` with `cap`, `callGas`, `stateGas`, `delta`, `reservoir`; prove the unsoundness condition, not a client-specific claim.
- Add a negative control at `tx.gas ≤ 2^24`.
- If a client repro is impossible in the timebox, ship the Lean statement + exact missing observation and say so.

**Adjacent decision — 8246 vs 7708.**
- Ask EF whether 8246 remains in scope or is superseded by 7708 per-wei logs.
- Keep C9 isolated so it can be retired without touching C1–C8.

**Acceptance:** both gaps are either proved or explicitly `GAP` with a witness and a named missing lemma; no silent gap.

### WS4 — Address-level impact evidence

**Problem:** the current register is strong at mechanism level but thin at address level. Pattern matching produces false positives; EF needs confirmed, reproducible rows.

**Plan.**
1. Build a dual-execution harness: same pinned block and pre-state, Osaka vs pinned Amsterdam EELS; record `(tx.gas, gasLeft, stateGasLeft)` before/after.
2. Resolve implementations through EIP-1967 slots; never test a proxy shell.
3. Require untrusted-caller reachability and a real divergence: permanent state after failed subcall, or revert where Osaka succeeded.
4. Priority order:
   - ERC-4337 `EntryPoint` v0.6/0.7/0.8 (`innerHandleOp`, `eth_estimateUserOperationGas`).
   - OP-Stack `CrossDomainMessenger` / `OptimismPortal` (`SafeCall.callWithMinGas`, failed-message marking).
   - 7702 delegate `initialize` / `setup`.
   - DEX/lending lock flags `0 → 1 → 0`.
   - Oracle callback budgets; bridge destination gas.
5. Keep inferred rows in Appendix A only. Mark sensitive rows `EMBARGOED`; report by email, not public issue.

**Acceptance:** ≥20 confirmed rows, or a documented “none found” per class with search method and block range. Every row has a one-command repro.

### WS5 — EF package and review

**Plan.**
1. Send `docs/ef-report.md` (one page) plus `docs/spec-cards.md` (appendix) to `glamsterdam@ethereum.org`.
2. Ask four concrete decisions: (a) is C1–C4 the right review surface? (b) is 8246 still in scope? (c) does the client expose state gas to estimators? (d) which findings need a local repro before the next ACD?
3. Run a red-team quorum on the top 10 rows before sending; record dissent in `docs/quorum-log.md`.
4. Offer a 30-minute walkthrough; do not publish exploit details.

**Acceptance:** EF receipt, four answers or explicit “deferred”, and a follow-up date.

### WS6 — CI, release, and maintenance

**Plan.**
1. Add CI checks: `make check`; card mutant suite; link check for every card source range; schema validation for `claims.jsonl`.
2. Add a `fork_variant` matrix build so D0/D13R/D13A cannot silently drift.
3. Tag a review release (`v0.2.0-audit`) after WS1–WS4; keep `main` green.
4. Maintenance: any spec pin change requires re-running the 12 mutants and the dual-execution harness.

**Acceptance:** a red CI run blocks merge; a spec-pin bump has a documented revalidation checklist.

## 2. Timeline (6 weeks, part-time)

| Week | WS1 core | WS2 cards | WS3 gaps | WS4 evidence | WS5 EF |
|---|---|---|---|---|---|
| 1 | `ForkParams` + `MeterCore` skeleton | Freeze IDs/schema; C1/C3/C2/C4 mutants | 7702 trace outline | Harness design; 4337 target | Draft one-pager |
| 2 | `CallStack`; D0/D13R/D13A instantiations | C5–C8 mutants | 7702 lemmas | 4337 + OP Stack rows | Internal review |
| 3 | `Refine.lean` statement + easy direction | C9–C12; split any multi-claim card | Estimator Lean statement | 7702 + DEX rows | Quorum review |
| 4 | Remove `D13AMeter`; delete duplicates | Full mutant suite green | Estimator witness / negative control | Oracle/bridge rows | Send report |
| 5 | Performance + LoC reduction | Reviewer README final | 8246/7708 decision recorded | ≥20 rows or documented none | EF walkthrough |
| 6 | Release tag | Publish cards | Gap register final | Evidence appendix | Follow-up |

## 3. Risks and mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| Spec changes again (D1/D3/D4) | Cards and core drift | `ForkParams` is the only fork surface; CI matrix re-runs mutants on pin change |
| 8246 is pulled in favour of 7708 | C9 wasted effort | Keep C9 isolated; ask EF before deepening |
| No address-level exploit found | Weak evidence | Report mechanism-level rows + exact search method; do not overclaim |
| Client cannot expose state gas | Estimator fix stalls | Ship the Lean condition + recommended RPC change; do not block the report |
| Public disclosure risk | Harm to users | Embargo sensitive rows; email EF; no public issue |
| Agent/tooling instability | Delays | Run the critical path manually; agents only for parallel evidence gathering |

## 4. Budget

- Formal core + cards: ~2 engineer-weeks.
- Evidence harness + 20 rows: ~2 engineer-weeks.
- EF package + review: ~3 engineer-days.
- VM/token budget: keep under the existing daily cap; no long-lived VMs; destroy after each lane.

## 5. Deliverables

1. `Glamsterdam/SpecCore/{ForkParams,MeterCore,CallStack,Refine}.lean`
2. `docs/spec-cards.md` + mutant suite
3. `docs/estimator-safety-spec.md` with witness or `GAP`
4. `docs/impact-register.md` with ≥20 confirmed rows or documented none
5. `docs/ef-report.md` (one page) + `docs/spec-cards.md` appendix
6. `docs/quorum-log.md` with red-team dissent
7. Tag `v0.2.0-audit`, green CI
