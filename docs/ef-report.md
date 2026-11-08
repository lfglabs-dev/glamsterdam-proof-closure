# Glamsterdam gas invariants — what breaks, what is unproven, what to fix

**To:** `glamsterdam@ethereum.org`
**From:** Verity / Glamsterdam proof-closure audit
**Date:** 2026-11-07
**Pinned spec:** `ethereum/execution-specs@16898000` (`Amsterdam D0`)
**Status:** mechanism-level results confirmed; address-level repros in progress. Please treat this as a request for review, not a disclosure.

## 1. What we checked

We mapped our 60 Lean guarantees to EF's 8 invariants and built 12 small review cards: one statement, one source range, one witness, one mutant each. The full set is `docs/spec-cards.md`. The three failure modes below are the ones we believe matter most.

## 2. Three confirmed failure modes

### A. A failed call no longer prevents the caller from writing state
- A callee can run out of gas and fail, yet the caller's failure handler can still write a fresh storage slot.
- The reservoir pays the 97,920 state-gas part; only ~12,100 execution gas is needed for a cold write.
- Result: the caller permanently records "failed" where Osaka would have reverted. Retries are lost.
- Affects: fixed-grant calls, `try/catch` failure handling, relayers, bridges, 4337.

### B. Clearing a slot in the same transaction returns 97,920 gas immediately
- `0 → 1 → 0` on a slot that was zero at transaction start gives the state gas back at the clear.
- That can push `gasleft()` above a post-call "was this underfunded?" check.
- Result: a griefing attempt that should revert can finish and record a permanent failure.
- Affects: lock/flag patterns, batch executors, hooks around external calls.

### C. A reverting intermediary returns gas it already spent
- In `C → D → E`, if `D` creates state and then reverts after `E` OOGs, `D` returns unused gas **plus** the refunded state-creation gas.
- The outer contract sees more gas than the old model predicts and may pass its safety check.
- Result: a nested OOG no longer implies "the caller has almost nothing left".
- Affects: multicall, routers, account abstraction, any contract that infers failure cause from remaining gas.

## 3. Two things we have not proved

1. **7702 replay.** A 7702 delegation that OOGs is rolled back, but the transaction is mined and the signed authorization stays valid. An attacker can reuse it and call an unprotected `initialize`. We have the mechanism, not a full formal trace. Treat as `GAP`.
2. **Estimator safety.** An honest `eth_estimateGas` / `eth_estimateUserOperationGas` binary search over `gasleft()` deltas can miss reservoir draws when `tx.gas > 2^24`. The condition is clear; a client-level repro is still pending. This is the Pimlico/4337 case.

## 4. What we recommend

**For contracts**
1. Make failed work retryable. Do not write a permanent "done/failed" marker on a failure path you cannot retry.
2. Use transient storage for locks and flags; do not rely on a same-tx `0 → 1 → 0` refund.
3. Do not bill by `gasleft()` differences. Charge an agreed fee, or clamp and cap the measurement.
4. Make gas budgets adjustable; size for a first-time recipient and a fresh slot.
5. Check `CREATE` / `CREATE2` results; do not infer the cause of failure from empty revert data.
6. For 7702, bind `initialize` to the account's own signature or a self-call, and use namespaced storage.

**For clients / RPC**
7. Expose `state_gas_left` in `eth_call` / `eth_estimateGas`, or simulate with the reservoir disabled, and add a safety margin.
8. Treat a mined type-4 transaction as proof only after reading the account's resulting code.

## 5. What we ask from EF

1. Confirm that cards **C1–C4** (failed-call parent write, same-tx clear, revert return, fixed budgets) are the right review surface for the next ACD.
2. Confirm whether **EIP-8246** is still in scope or superseded by 7708 per-wei logs.
3. Tell us whether clients plan to expose state gas to estimators, or whether the expected fix is “simulate without the reservoir”.
4. Point us at any affected project where you want an address-level repro first; we will keep sensitive rows embargoed and report by email.

## 6. Appendix

- 12 cards, one page each: `docs/spec-cards.md`
- Mechanism-level impact rows and inferred hypotheses: `docs/impact-register.md`
- Estimator statement and witness requirements: `docs/estimator-safety-spec.md`
- Reviewer path: `docs/README-spec-review.md`
- Pinned theorem map: `docs/ef-invariants-map.md`

**Contact:** reply to this thread; we can walk through any card in 30 minutes. No exploit details are included in this report.
