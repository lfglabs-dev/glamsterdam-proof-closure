# Simplification Plan — one trusted core, twelve cards

**Status:** draft for review, 2026-11-07
**Constraint:** additive first. Do not rename or delete existing theorems or C-ABI symbols until the new layer is green and the old layer is a proved projection.

## 1. The problem

The current model carries four overlapping meters (`EvmGasFrame`, `GasMeter`, `CallFrameMeter`, `D13AMeter`) and an 8-way `ForkSchedule × AllowanceMode` product. The same fact is proved in several places, so a reviewer has to trust a large surface. The fix is not “more theorems”; it is one small state type, six partial transitions, and one refinement obligation.

## 2. Target trusted core

| File | Contents | Reviewer question |
|---|---|---|
| `Glamsterdam/SpecCore/ForkParams.lean` | `Policy` record: `refill`, `revertSpill`, `allowance`; `ForkParams` = `{policy, reservoirThreshold := 2^24}`. D0/D13R/D13A are three values, not three copies. | Is every behavioural fork a field here, and nothing else? |
| `Glamsterdam/SpecCore/MeterCore.lean` | `allocate_tx_gas` (2^24 split), `charge_exec`, `charge_state` (legacy share + optional ceiling), `credit_state_refund`, `settle_tx_gas`. | Does every state-gas transition go through these five functions? |
| `Glamsterdam/SpecCore/CallStack.lean` | `pushFrame` (63/64 cap, reservoir forward, DELEGATECALL ceiling inheritance vs CALL/CREATE cap), `popFrame` (success/revert/halt, 7702 entry rollback). | Is the 63/64 rule stated once? |
| `Glamsterdam/SpecCore/Refine.lean` | Projection to `Glamsterdam/Gas/Meter.lean`, `Journal.lean`, `Frame.lean`; one `refines` theorem per transition. | Does the abstraction preserve `stateGasBaseline` and `stateGasSpilled`? |
| `docs/spec-cards.md` | 12 cards, each one statement + one source range + one witness + one mutant. | Can an auditor read one card without the rest? |

## 3. Delete / move / keep

| Item | Decision | Reason |
|---|---|---|
| `ForkSchedule` × `AllowanceMode` product | **Collapse** into `ForkParams` | The variants differ in three behaviours, not eight proofs. |
| `MetaSpec` combinators, `WitnessRefuter`, audit linter | **Move** to `audit/tools/` | Review tooling, not proof assumptions. |
| Duplicate per-variant `CallTree` lemmas | **Keep one generic lemma + three instantiations** | Shrinks the trusted set without losing the D0/D13R/D13A witnesses. |
| `D13AMeter` as a separate type | **Delete after `Refine.lean`** | It is `ForkParams` with `allowance := perFrame12582`; keeping both invites drift. |
| `EvmGasFrame` / `CallFrameMeter` compatibility shims | **Keep during migration, delete after projection** | Needed for `make check` and C-ABI stability. |
| `audit/evm-gas-semantics-lean-phase2/NeedExact.lean` | **Keep** | It is the honest boundary for the estimator gap (`NoCatch`, `NoIfGas`). |
| 8246 / 7732 / 8282 audit files | **Keep**, cite from cards C9–C11 | Adjacent audits; they are not part of the gas core. |

## 4. The one refinement obligation

```lean
theorem specCore_refines_eels
  (f : ForkParams) (s : EelsState) (t : Tx) :
  eelsRun f s t = some s' →
  ∃ c, specRun f (project f s) t = some c ∧ project f s' = concretize f c
```

If this is not proved, the delta abstraction is a model, not a refinement. The card witnesses are valid inside the model; the refinement is what lets an EF reviewer connect them to the pinned EELS.

## 5. Migration order

1. Add `ForkParams.lean` + `MeterCore.lean`; prove the five transitions against the existing `GasMeter` (no deletions).
2. Add `CallStack.lean`; instantiate D0, D13R, D13A; re-derive the four band lemmas as corollaries.
3. Add `Refine.lean`; state the obligation; prove the easy direction first.
4. Publish `docs/spec-cards.md`; run the quorum review on C1, C3, C2, C4.
5. Only then remove `D13AMeter` and the duplicated per-variant lemmas; keep shims until the C-ABI test is green.

## 6. What this does not fix

- The estimator gap (Card C5/C6 witness, `docs/estimator-safety-spec.md`) remains a client/RPC property.
- Deployed-contract prevalence remains an external scan (`docs/impact-register.md`), not a Lean theorem.
- 8246 may be superseded by 7708 per-wei logs; the card is written so it can be retired without touching C1–C8.
