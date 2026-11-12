# Quorum Log — Glamsterdam audit, 2026-11-07

Purpose: record what the review models changed before we spent implementation time. Only decisions that altered the work are kept.

## Q1 — pre-launch review (antigravity/agy-model-high, completed)

**Verdict:** launch is sound, but not with a moving theorem namespace and an unfrozen claim schema.

Adopted:
1. **Freeze the claim schema before lanes write.** Add `fork_variant ∈ {D0, D13R, D13A}` and `card ∈ C1..C12`; a claim that flips truth across variants is invalid without it. Main register = confirmed only; inferred goes to an appendix.
2. **Keep L4 additive.** No theorem renames, no C-ABI changes, `make check` green throughout. The new `SpecCore/` is a projection over existing modules until `Refine.lean` lands.
3. **Harden L1.** Require untrusted-caller reachability, EIP-1967 implementation resolution, and dual execution (Osaka vs pinned Amsterdam at the same block). Pattern matches alone are not rows.
4. **Collapse the meter product.** One `FrameStack` + one `Policy` record (`refill`, `revertSpill`, `allowance`), five meter transitions, two stack transitions. This is the same direction as `docs/simplification-plan.md`.
5. **Prioritize the two live tripwires.** ERC-4337 `EntryPoint` (`innerHandleOp` + `eth_estimateUserOperationGas`) and OP-Stack `CrossDomainMessenger` / `OptimismPortal` (`SafeCall`, failed-message marking). These hit C1/C4/C5/C6/C7 together.
6. **Evidence gate.** Every main-table row needs a deterministic single-command repro against pinned EELS or a pinned client RPC, plus exact `(tx.gas, gasLeft, stateGasLeft)` before/after.

Not adopted as-is:
- Renaming C-ABI symbols is out of scope for this pass; shims stay until the projection is proved.
- 12 cards remain one file (`docs/spec-cards.md`); splitting into 12 files is cosmetic and makes review harder.

## Q2 — spec-core design review (gemini-4-carbon, fable, astra)

Status: **blocked, not answered.** The consultant lanes were cancelled after repeated `library-skills-*.tar.gz` missing-file and inference-connection failures. No Q2 decisions were adopted. Re-run when the remote lane works; do not treat this as silent approval.

Questions asked: 3-file split vs merge/split; which cards are not single statements; minimum `ForkParams`; what to delete; the one refinement obligation; first card an EF auditor should read.

## Q3 — findings red-team

Pending. Will run on the merged top-20 claims before publication.

## Q4 — 11 Nov delta triage (manual; quorum unavailable)

Status: **manual review, not a model quorum.** Q2 lanes are still blocked, so this records only decisions forced by the new Signal/GitHub facts.

Adopted:
1. **Add the Uniswap v4 fixed-budget case as external evidence.** It has exact coordinates and fork measurements, but it stays “external, rerun pending” until we reproduce it.
2. **Add C13 candidate: fixed-budget call outcome must not depend on `tx.gas`.** Keep C1–C12 frozen; do not renumber or silently fold C13 into an existing card.
3. **Send the EF one-pager before ACDT #103 (16 Nov).** Do not wait for the independent Uniswap rerun; label the evidence honestly.
4. **Treat `8037-findings` as a triage worklist.** EF estimates ~80% false positives; raw entry counts are not blast radius.
5. **Use the 11 Nov OP testnet upgrade and the new OP-Stack contact** to unblock address-level OP evidence after ACDT.

Not adopted:
- Adding C13 to the main schema before a real quorum. Keep it an explicitly labelled candidate so the frozen C1–C12 review surface stays stable.
- Re-running the full pre-launch quorum on the delta. The remote lanes are still failing; a manual record is better than a fake approval.
