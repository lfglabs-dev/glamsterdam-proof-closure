# Glamsterdam Proof Closure

Lean 4.31 formal verification monorepo for the Ethereum Glamsterdam upgrade audits, verified with [`turbo-lean`](https://github.com/Th0rgal/turbo-lean) (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`).

## Pinned Upstream Targets

| Upstream Repository | Pinned Commit / Tag | Scope |
|---|---|---|
| `ethereum/execution-specs` | `16898000911c1e3caa57be08509536c10ae92d3e` (Oct 20, 2026) | `src/ethereum/forks/amsterdam/` (`EIP-8246`, `8037`, `8038`, `2780`, `7778`) |
| `ethereum/consensus-specs` | `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`, Oct 19, 2026) | `specs/gloas/beacon-chain.md` and `specs/gloas/fork.md` (`EIP-7732`) |
| `ethereum/EIPs` | `ed9b712640c1646dfda7ccceca2e0fd936b6472f` (Oct 20, 2026) | Normative EIP specifications (`8246`, `8037`, `8038`, `2780`, `7778`, `7732`, `8282`) |
| `lfglabs-dev/eip-8282-proof-closure` | `303a07d112d8aa51178c5d99c8e185b18bfddba7` | `EIP-8282` predeploy guarantees (`P-SUBMIT-1`, `P-DRAIN-1`, `P-CONTROL-1`) |

## Architecture

1. **`Glamsterdam/Common/Prelude.lean`**: State-preserving `Result ε σ α` and `SpecM σ ε α` monad, checked/saturating arithmetic helpers (`checkedSub?`, `saturatingSub`, `checkedAddU64?`, `ceil32`), and Layer-0b `@[simp]` equation lemmas.
2. **`Glamsterdam/Common/MetaSpec.lean`**: Meta-specification combinators (`Costed`, `MetaGateSpec`, `MetaAlgorithmSpec`, `FrameInvariant`, `ExactDeltaSpec`, `WitnessRefuter`, `MutantKillBundle`, `NonVacuousSpec`, `OutcomePartitionSpec`, `AccountingBoundarySpec`, `OrderIndependence`).
3. **`Glamsterdam/Common/ElCore.lean`**: Full-fidelity Execution Layer transcription (`Account`, `PreState`, `BlockState`, `TransactionState`, `GasMeter`, state-journal snapshots/rollbacks, 2D gas charging/spill/LIFO refund, and C-ABI exports).
4. **`Glamsterdam/Eip8246/Spec.lean`**: `EIP-8246` guarantees (`T-8246-BALANCE-PRESERVED`, `T-8246-SAME-TX-CREATE-DESTROY`, `T-8246-TX-STATE-CLEAR-EXACT`, `T-8246-SELFDESTRUCT-CONSERVATION`, `T-8246-NO-STATE-GAS-REFUND`, `T-8246-CLEAR-ORDER-INDEPENDENCE`, `T-8246-TX-FEE-SETTLEMENT-CONSERVATION`, `T-8246-ETH-CONSERVATION`, `T-8246-BAL-PATCHED-SOUND`) and refuters (`M-8246-1`, `F-8246-BAL-STORAGE-CLEARS-IGNORED`).
5. **`Glamsterdam/Gas/Spec.lean`**: Coupled gas guarantees (`EIP-8037`, `8038`, `2780`, `7778`): `T-8037-CHARGE-GAS-SOUND`, `T-8037-RESERVOIR-ROUNDTRIP-SUCCESS`, `T-8037-RESERVOIR-ROUNDTRIP-ERROR`, `T-8037-MESSAGE-CALL-GAS-AFFORDABLE`, `T-8037-ALLOCATE-EVM-GAS-SOUND`, `T-7778-8037-DUAL-CAP`, `T-8038-2780-WARM-COLD`, and refuters (`M-8037-1`, `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS`, `F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE`).
6. **`Glamsterdam/Gloas7732/Spec.lean`**: `EIP-7732` (+ `EIP-8282`) consensus state transition guarantees (`T-7732-SLASHED-NO-RESURRECTION`, `T-7732-BUILDER-SOLVENCY`, `T-7732-BUILDER-WITHDRAWAL-NO-UNDERFLOW`, `T-7732-EXIT-SAFETY`, `T-7732-QUORUM-NO-DOUBLE-COUNT`, `T-7732-DEFERRED-EXEC-EQUIV`, `T-7732-FRAME`, `T-8282-7732-QUEUE-SAFETY`) and refuters (`F-7732-SLASHED-PAYMENT-RESURRECTION`, `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP`, `F-7732-FORK-SLOT-AVAILABILITY`, `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER`).
7. **`Glamsterdam/TestVectors.lean`** & **`tests/differential/test_glamsterdam_differential.py`**: Kernel-checked test vectors (`by decide` / `by rfl`) and C-ABI differential testing against Python reference models (`pytest`).
8. **`audit/findings/GLAMSTERDAM-AUDIT-REPORT.md`**: Consolidated report of all 12 verified findings across CL (`7732/8282`) and EL (`8246`, `8037`, `8038`, `2780`, `7778`).

## Quick Verification

```bash
make check
```
