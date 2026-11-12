# Glamsterdam gas invariants — what breaks, what is unproven, what to fix

**To:** `glamsterdam@ethereum.org`
**From:** Verity / Glamsterdam proof-closure audit
**Date:** 2026-11-11
**Pinned spec:** `ethereum/execution-specs@16898000` (`Amsterdam D0`)
**Status:** mechanism-level results confirmed; one external address-level repro (Uniswap v4) pending our independent rerun. Please treat this as a request for review, not a disclosure.

## 0. What changed since 7 Nov

- **ACDT #103 is 16 Nov 2026, 14:00 UTC.** Agenda: audit status (reports expected 16–19 Nov), app-team contract findings, and open Q&A on the invariants repo. ACDE is 19 Nov; both auditors are invited to summarize.
- **OP upgraded its testnet.** EF review chat, 11 Nov: “OP successfully upgraded test net”; OP will connect EF to someone who can explain how it communicates changes to the rest of the OP Stack.
- **Uniswap and Shiba expect fixes by Jan.** Pimlico reports real ERC-4337 user flows broke on Sepolia after 8037; their workaround caps simulation at `16,777,216`, which excludes state-heavy ops.
- **No protocol fix has merged.** `EIPs#12581` and the `RESERVOIR` opcode proposal `EIPs#12577` remain open. The live options discussed are: ignore the breakages, move to EOF, lower the state-gas coefficient, or pull 8037 (estimated 3–5 months delay).
- **`8037-findings` is a worklist, not a blast-radius count.** EF chat says ~80% of entries are likely AI false positives. Known false-positive classes include changeable EOA gas, underflow with no state-changing op, and Uniswap Permit2’s 5,000-gas cap (mitigated by an access list).
- **Banteg’s “200k contracts broken” is unverified.** The arachnid CREATE2 factory is already on mainnet, is not deployable on new chains, and EIP-7997 enshrines it; treat the number as a comms claim, not evidence.

## 1. What we checked

We mapped our 60 Lean guarantees to EF's 8 invariants and built 12 small review cards: one statement, one source range, one witness, one mutant each. The full set is `docs/spec-cards.md`. The four failure modes below are the ones we believe matter most; the fourth is an external report that is not yet one of the eight invariants.

## 2. Four confirmed failure modes

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

### D. A fixed-budget subcall’s outcome depends on `tx.gas`
- Uniswap v4 `PositionManager` calls `notifyUnsubscribe{gas: 150_000}` and catches failure.
- At `tx.gas ≤ 2^24` the call OOGs and the catch ignores it: 172,044 gas used. At 16.9M the reservoir pays the state gas and the same call succeeds: 255,543 gas used.
- `eth_estimateGas` returns 169,842, i.e. the failing path. The same calldata and state therefore take different paths depending on a number the sender or bundler chooses.
- Result: subscribers are silently skipped, their state goes stale, and a fixed gas budget no longer gives a deterministic outcome.
- Affects: hooks, subscribers, relayers, ERC-4337, intents, and every `call{gas: X}` that can create state.
- Proposed invariant: a call with a fixed gas budget must not change outcome based on `tx.gas`. This is outside EF’s current eight invariants.
- Source: Uniswap public report (Daniel Gretzke), mainnet-fork measurement. Gas-accounting mechanism proved in `Glamsterdam.Gas.Spec.t_8037_c13_fixed_budget_subcall_tx_gas_dependent` (`txGas = 500,000` vs `16,900,000` for `subcallCap = 150,000`); our independent mainnet-fork bytecode rerun is pending (`GAP`), so treat the deployed address numbers as external evidence.

## 3. Two things we have not proved

1. **7702 replay.** A 7702 delegation that OOGs is rolled back, but the transaction is mined and the signed authorization stays valid. An attacker can reuse it and call an unprotected `initialize`. We have the mechanism, not a full formal trace. Treat as `GAP`.
2. **Estimator safety.** An honest `eth_estimateGas` / `eth_estimateUserOperationGas` binary search over `gasleft()` deltas can miss reservoir draws when `tx.gas > 2^24`. The aggregate budget condition and negative control are proved in `Glamsterdam.Gas.Spec.estimator_unsound_above_2pow24` and `allocation_zero_reservoir_below_2pow24` (`docs/estimator-safety-spec.md`). Pimlico reports this broke real Sepolia user flows and now caps simulations at `16,777,216`; ChainSecurity independently agrees honest estimators trigger it. The off-chain incident and budget-level condition are confirmed; an independent client/RPC binary-search trace is still `GAP`. This is the Pimlico/4337 case.

## 4. What we recommend

**For contracts**
1. Make failed work retryable. Do not write a permanent "done/failed" marker on a failure path you cannot retry.
2. Use transient storage for locks and flags; do not rely on a same-tx `0 → 1 → 0` refund.
3. Do not bill by `gasleft()` differences. Charge an agreed fee, or clamp and cap the measurement.
4. Make gas budgets adjustable; size for a first-time recipient and a fresh slot.
5. Check `CREATE` / `CREATE2` results; do not infer the cause of failure from empty revert data.
6. For 7702, bind `initialize` to the account's own signature or a self-call, and use namespaced storage.
7. Do not give a state-creating subcall a fixed `{gas: X}` unless the outcome is allowed to change with `tx.gas`. Prefer a deterministic all-or-nothing path, or pass enough gas and handle failure explicitly.

**For clients / RPC**
8. Expose `state_gas_left` in `eth_call` / `eth_estimateGas`, or simulate with the reservoir disabled, and add a safety margin.
9. Treat a mined type-4 transaction as proof only after reading the account's resulting code.

## 5. What we ask from EF

1. Confirm that cards **C1–C4** (failed-call parent write, same-tx clear, revert return, fixed budgets) plus the Uniswap fixed-budget case are the right review surface for ACDT on 16 Nov.
2. Confirm whether **EIP-8246** is still in scope or superseded by 7708 per-wei logs.
3. Tell us whether clients plan to expose state gas to estimators, or whether the expected fix is “simulate without the reservoir”.
4. Point us at any affected project where you want an address-level repro first; we will keep sensitive rows embargoed and report by email.
5. Will EF adopt a deterministic fixed-budget-call rule before scheduling, or document the `tx.gas`-dependent outcome as an accepted break? `EIPs#12581` remains open and does not fix it.

## 6. Appendix

- 12 cards, one page each: `docs/spec-cards.md`
- Mechanism-level impact rows and inferred hypotheses: `docs/impact-register.md`
- Estimator statement and witness requirements: `docs/estimator-safety-spec.md`
- External Uniswap v4 report and gas measurements: https://gist.github.com/rahul-kothari/0b5ca3cd94a0ed262c063337483d4754
- Reviewer path: `docs/README-spec-review.md`
- Pinned theorem map: `docs/ef-invariants-map.md`

**Contact:** reply to this thread; we can walk through any card in 30 minutes. No exploit details are included in this report.
