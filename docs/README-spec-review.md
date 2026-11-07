# Reviewer README — how to audit the Glamsterdam specs in 20 minutes

**Audience:** EF auditor, client engineer, or external reviewer who wants the shortest path to “do I trust this?”

## 1. Read four files, in this order

1. `docs/spec-cards.md` — Cards 1, 3, 2, 4. These are the silent-failure mechanism and its immediate consequences.
2. `docs/estimator-safety-spec.md` — the off-chain hazard; one statement, one witness, one negative control.
3. `docs/simplification-plan.md` — the trusted core (`ForkParams` + 5 meter transitions + 2 stack transitions) and the one refinement obligation.
4. `docs/impact-register.md` — what is actually deployed; confirmed vs inferred is explicit.

## 2. What each card gives you

- **One statement.** No conjunction of unrelated facts.
- **One source range.** A line range in pinned EELS or the consensus spec.
- **One witness.** A theorem that instantiates the statement.
- **One mutant.** The edit that should make the witness fail. If the mutant still passes, the card is vacuous.
- **One confidence label.** `proved`, `proved-under-assumptions`, or `GAP`. No silent gaps.

## 3. The five questions to ask

1. **Is the statement non-vacuous?** Does the mutant actually break it?
2. **Is the reservoir explicit?** Cards 1, 5, 7, 8 must mention `stateGasSpilled` / `stateGasLeft`, not just `gasLeft`.
3. **Is the fork a parameter?** A card that is true only for D0 or only for D13S must say so via `fork_variant`.
4. **Is the refinement stated?** The delta abstraction is only trusted if `specCore_refines_eels` is proved or clearly marked as the open obligation.
5. **Is the evidence real?** Impact rows need a pinned block, resolved implementation hash, source line, reachability, and a dual execution — not a bytecode pattern.

## 4. What is deliberately not claimed

- Client behaviour (`geth`/`reth`/`nethermind`) and RPC estimators are outside the Lean model; `docs/estimator-safety-spec.md` states the condition, not a client proof.
- Deployed-contract prevalence is an external scan; it is evidence for prioritization, not a theorem.
- 8246 is written so it can be retired if 7708 per-wei logs supersede it; Cards 1–8 do not depend on it.
- INV-8 / 7702 replay is a `GAP` until the full mined-but-rolled-back trace is formalized.

## 5. Fast falsification tests

| Card | Run this | Expected |
|---|---|---|
| C1 | Remove `restore_state_gas` on child revert | Parent write OOGs; theorem fails |
| C2 | Use Osaka refund-at-settlement | Same-tx clear no longer returns 97,920 immediately |
| C3 | Skip failed-`CREATE` refund | Parent sees 183,600 less; theorem fails |
| C4 | Restore Osaka prices | 50,000-grant witness disappears |
| C5 | Assume global `gasleft()` monotonicity | D13R cross-frame rise witness fails |
| C6 | Assume retained 1/64 < failure cost | Band witness fails |
| C7 | Let sentry see reservoir | 2,300-stipend theorem fails |
| C8 | Assume clear cannot raise `gasleft()` | D13S helper-clear witness fails |
| C12 | Assume mined ⇒ delegation applied | OOG replay witness fails |

If a test does not fail where the table says it should, the card is too weak or the model is wrong. Report that first.
