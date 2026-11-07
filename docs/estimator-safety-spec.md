# Estimator Safety Spec — `eth_estimateGas` under EIP-8037

**Status:** draft statement, 2026-11-07. No proof yet.
**Scope:** off-chain estimator / `eth_call` binary search over `gasleft()` deltas when `tx.gas > 2^24` (16,777,216). This is outside the EELS transition model; it is a client/RPC property.

## Hazard

A caller estimates gas by binary-searching a gas cap `g` on `eth_call`, accepting the smallest `g` for which the call succeeds. With EIP-8037, part of the cost is paid from `state_gas_reservoir` and is invisible to the outer `gasleft()`. Two failures follow:

1. **Underestimate.** The estimator accepts `g` because the outer `gasleft()` delta fits, but the real transaction needs more state gas than the reservoir can supply at that cap, so it OOGs or leaves work unaccounted.
2. **False success.** The call appears to succeed under `eth_call` because reservoir gas is available, but the mined transaction at `g` fails (or vice versa).

The known instance is Pimlico `eth_estimateUserOperationGas` / `eth_call` with ERC-4337 `EntryPoint`, reported 29 Oct. and relayed by Rahul (EF).

## Target Lean statement

```lean
structure Estimator where
  cap        : Nat
  callGas    : Nat
  stateGas   : Nat
  delta      : Nat          -- observed outer gasleft() delta
  reservoir  : Nat          -- invisible to delta
  ok         : Bool

def honest (e : Estimator) : Prop :=
  e.delta = e.callGas ∧ e.reservoir = e.stateGas

def accepts (e : Estimator) : Prop :=
  e.ok = true ∧ e.cap = e.delta

theorem estimator_unsound_above_2pow24
  (e : Estimator)
  (hcap   : e.cap > 2^24)
  (hhonest: honest e)
  (hdelta : e.delta < e.callGas + e.stateGas) :
  ∃ e', accepts e' ∧ ¬ e'.ok
```

**Reading:** for any honest estimator whose measured delta omits the reservoir draw, there is an accepted cap at which the real execution does not succeed. The witness must give the concrete `(cap, callGas, stateGas, delta, reservoir)` tuple and the client trace.

## Mandatory evidence before this becomes a theorem

1. A minimal contract/trace where `eth_call` succeeds at cap `g` and the same transaction at `g` fails or leaves unaccounted state gas.
2. The measured `gasleft()` deltas on both sides of the call, with the reservoir draw and `tx.gas > 2^24`.
3. The client + version + block number, and the exact RPC sequence.
4. A negative control at `tx.gas ≤ 2^24` where the estimator is sound.
5. A statement of what the estimator is allowed to assume (e.g. no access to `state_gas_left`).

## Non-goals

- This does not prove anything about the EVM transition itself; Cards 1–8 cover that.
- This does not claim all clients are affected; it gives the condition under which an honest binary-search estimator is unsound.
- This does not replace a client fix; the fix is either expose state gas to the estimator or clamp/cap the measurement.

## Candidate fixes (for the EF thread)

- Add `state_gas_left` / `state_gas_used` to the `eth_call` / `eth_estimateGas` result and require the estimator to account for it.
- Make the estimator simulate with the reservoir disabled (or with an explicit reservoir budget) and add a safety margin.
- For ERC-4337, stop billing by `gasleft()` deltas; charge the agreed fee and clamp the measurement.
