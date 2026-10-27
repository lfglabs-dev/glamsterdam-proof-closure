# Brief — direction of the Glamsterdam proof effort

**Challenge.** The difficult part is the interaction between EVM gas, state-gas reservoir/refill, refunds, child frames, and fork-specific ordering. Several apparent proof gaps were model defects, so counterexamples and statement review had to precede closure.

**Studied.** The work covered EIP-8037/8038/2780/7778 gas semantics, EIP-12582 delayed rollback credit, EIP-8246 account clearing, EIP-7732/8282 consensus transitions, and the enumerator completeness board. It compared Exec against EELS and required concrete witnesses plus negative controls.

**Direction.** The effort is converging on a source-pinned, executable audit: reusable invariants carry short Lean corollaries, each important claim has a concrete witness and mutation/refutation path, and each merge carries build, ledger, witness, and `turbo-lean` evidence. The jo completeness line is now at 146 board theorems, 142 witnessed, 4 allow-listed; PR #99's GAS witness is merged.

**Remaining.** Finish the four CallBridge-dependent entries, land R1/R2/R3 fixes with regressions, track the verifier thread-limit and cached sandbox-receipt defects while the lead restores the allowlist pin, and wait for the clean-check soundness fix before using CLEAN coverage claims. Signal/Hindsight refresh is pending secret approval in this session.

**Latest scope ruling.** (C) CLEAN remains void pending soundness repair; C′ on checker `067bca3` counts only modulo completeness/adversarial corpus, and NOT CLEAN without EELS replay is a candidate. Main/statement changes require the lead again; the existing proof teams retain their assigned scope.
