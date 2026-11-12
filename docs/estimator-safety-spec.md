# Estimator Safety Spec — `eth_estimateGas` under EIP-8037

**Status:** conditional aggregate-budget model proved in `Glamsterdam/Gas/Spec.lean` (2026-11-12); live client/RPC trace remains `GAP`.
**Scope:** off-chain delta-based gas estimation over `allocate_evm_gas` when `tx.gas > 2^24` (`TX_MAX_GAS_LIMIT = 16,777,216`). The Lean formalization covers the conditional aggregate gas-budget partition and EELS `GasMeter` fixed-budget subcall accounting; full client/RPC binary-search behavior and live contract bytecode reproduction remain outside the EELS transition model.

## Hazard

When `tx.gas > 2^24`, `allocate_evm_gas` caps `execution_gas` at `2^24 - intrinsic.execution` and places the excess into `state_gas_reservoir`. State-creation charges draw from `state_gas_reservoir` first and do not reduce `gas_left` (`GAS` / `gasleft()`).

1. **Delta underestimate (`estimator_unsound_above_2pow24`).** Assume a probe at `cap > 2^24` where `budgetFits` holds (`e.ok = true`) and a candidate limit `cap' = intrinsicExec + delta` with `delta = callGas`, omitting positive `stateGas`. Then the probe reservoir is positive, while `cap' ≤ 2^24` receives `stateGasReservoir = 0` and fails the aggregate budget check (`budgetFits = false`). The delta equality is an assumption, not a derived `gasleft()` trace; the general hypotheses do not require the reservoir to cover all state gas. The concrete witness below does have enough reservoir to cover its state charge.
2. **Fixed-budget subcall `tx.gas` sensitivity (`t_8037_c13_fixed_budget_subcall_tx_gas_dependent`).** A parent transaction that invokes a caught fixed-budget subcall `call{gas: subcallCap}` (`run_fixed_budget_caught_subcall`) forwards `stateGasLeft` via `drain_state_gas_reservoir`. For the concrete EELS `GasMeter` parameters `(intrinsicExec = 21,000, preExecGas = 50,000, subcallCap = 150,000, subcallExecNeed = 60,000, subcallStateNeed = STATE_GAS_STORAGE_SET = 97,920)`, the outer transaction succeeds at both `txGas = 500,000` and `txGas = 16,900,000`, but the subcall OOGs and is rolled back at `500,000` (`some (true, false)`) while succeeding at `16,900,000` (`some (true, true)`).

The reported off-chain instances are Pimlico `eth_estimateUserOperationGas` / `eth_call` with ERC-4337 `EntryPoint` and the external Uniswap v4 `PositionManager.notifyUnsubscribe{gas: 150_000}` report.

## Correction to the 2026-11-07 draft target

The initial draft wrote `def accepts (e : Estimator) : Prop := e.ok = true ∧ e.cap = e.delta` and asked for `∃ e', accepts e' ∧ ¬ e'.ok`, which was self-contradictory (`e'.ok = true` and `e'.ok = false` on the same record).

The proved specification separates the high-budget probe record `e` (`e.cap > TX_MAX_GAS_LIMIT`, `e.ok = true`) from the reduced candidate record `e'` (`e'.cap = e.intrinsicExec + e.delta`, `e'.ok = false`) via `acceptsAtDelta e e'`, and renames the aggregate budget check to `budgetFits` and the observation assumption to `observedBudget` so it is not confused with a full EVM bytecode execution oracle or a multi-step binary-search loop model.

## Proved Lean statements (`Glamsterdam/Gas/Spec.lean`)

```lean
structure Estimator where
  cap : Nat
  intrinsicExec : Nat
  callGas : Nat
  stateGas : Nat
  delta : Nat
  reservoir : Nat
  ok : Bool
  deriving Repr, DecidableEq, BEq

def budgetFits (cap intrinsicExec callGas stateGas : Nat) : Bool :=
  let alloc := allocate_evm_gas cap ⟨intrinsicExec, 0⟩
  decide (intrinsicExec ≤ cap) &&
    decide (callGas ≤ alloc.executionGas) &&
    decide (callGas + stateGas ≤ alloc.executionGas + alloc.stateGasReservoir)

def observedBudget (e : Estimator) : Prop :=
  let alloc := allocate_evm_gas e.cap ⟨e.intrinsicExec, 0⟩
  e.intrinsicExec ≤ TX_MAX_GAS_LIMIT ∧
  e.callGas ≤ TX_MAX_GAS_LIMIT - e.intrinsicExec ∧
  e.reservoir = alloc.stateGasReservoir ∧
  e.delta = e.callGas ∧
  e.ok = budgetFits e.cap e.intrinsicExec e.callGas e.stateGas

def acceptsAtDelta (e e' : Estimator) : Prop :=
  e.ok = true ∧
  e'.cap = e.intrinsicExec + e.delta ∧
  e'.intrinsicExec = e.intrinsicExec ∧
  e'.callGas = e.callGas ∧
  e'.stateGas = e.stateGas ∧
  e'.delta = e.delta ∧
  e'.reservoir = (allocate_evm_gas e'.cap ⟨e'.intrinsicExec, 0⟩).stateGasReservoir ∧
  e'.ok = budgetFits e'.cap e'.intrinsicExec e'.callGas e'.stateGas

theorem estimator_unsound_above_2pow24
    (e : Estimator)
    (hcap : e.cap > TX_MAX_GAS_LIMIT)
    (hobs : observedBudget e)
    (hok : e.ok = true)
    (hdelta : e.delta < e.callGas + e.stateGas) :
    e.reservoir > 0 ∧
    ∃ e' : Estimator,
      acceptsAtDelta e e' ∧
      e'.cap ≤ TX_MAX_GAS_LIMIT ∧
      e'.reservoir = 0 ∧
      e'.ok = false
```

- **Concrete witness (`highBudgetProbeWitness`, `reducedBudgetCandidateWitness`, `estimator_unsound_above_2pow24_witness`).** At `cap = 16,900,000`, `intrinsicExec = 21,000`, `callGas = 100,000`, and `stateGas = STATE_GAS_STORAGE_SET` (`97,920`), `highBudgetProbeWitness` has `reservoir = 122,784` and `ok = true`, while `reducedBudgetCandidateWitness` at `cap = 121,000 ≤ TX_MAX_GAS_LIMIT` has `reservoir = 0` and `ok = false`.
- **Allocation negative control (`allocation_zero_reservoir_below_2pow24`).** Whenever `intrinsic.execution ≤ txGas ≤ TX_MAX_GAS_LIMIT`, `allocate_evm_gas` yields `stateGasReservoir = 0` and `executionGas = txGas - intrinsic.execution`. This proves the allocation-level zero-reservoir property below `2^24` (not full client estimator soundness).
- **Fixed-budget caught subcall witness (`t_8037_c13_fixed_budget_subcall_tx_gas_dependent`).** Proves on `run_fixed_budget_caught_subcall` that the two concrete `txGas` witnesses `500,000` and `16,900,000` evaluate to `some (true, false)` and `some (true, true)` respectively.

## Residual client/trace `GAP`

1. **No client RPC / binary-search loop model.** `budgetFits` and `observedBudget` model a single step of delta-based candidate selection over `allocate_evm_gas` aggregate budgets; they do not model an iterative binary search over `eth_estimateGas` or `eth_estimateUserOperationGas`.
2. **No live client trace or Uniswap v4 bytecode reproduction.** `t_8037_c13_fixed_budget_subcall_tx_gas_dependent` is an EELS `GasMeter` transition witness (`run_fixed_budget_caught_subcall`), not an independent replay of deployed Uniswap v4 `PositionManager` bytecode or an Amsterdam client RPC session.
3. **Evidence still required to close the operational `GAP`:**
   - Client name, commit/version, fork configuration, and exact `eth_call` / `eth_estimateGas` / `eth_estimateUserOperationGas` RPC transcript above and below `2^24`.
   - Independent local rerun of the external Uniswap v4 `PositionManager.notifyUnsubscribe{gas: 150_000}` trace and ERC-4337 `EntryPoint` trace.

## Candidate fixes (for the EF thread)

- Expose `state_gas_left` / `state_gas_used` in `eth_call` / `eth_estimateGas` results and require delta-based estimators to include state gas.
- Simulate estimation with the state-gas reservoir disabled (or clamp the probed cap when constructing delta-based estimates) and add an explicit state-gas margin.
- For ERC-4337, avoid billing inner calls solely by `gasleft()` deltas when `tx.gas > 2^24`.

