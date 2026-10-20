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

1. **`Glamsterdam/Common/MetaSpec.lean`**: Layer I meta-specification combinators (`MetaGateSpec`, `MetaAlgorithmSpec`, `ObservationalProj`, `FrameInvariant`, `WitnessRefuter`).
2. **`Glamsterdam/Common/ElCore.lean`**: Shared 16-function Execution Layer core (`State`, `Account`, `TransactionEnvironment`, `Evm`, journal checkpoints, `move_ether`, `clear_account_preserving_balance`, `charge_gas`, child frame incorporation, and block/tx orchestration) plus `T-COMMON-CHECKPOINT-ROLLBACK`.
3. **`Glamsterdam/Eip8246/Spec.lean`**: `EIP-8246` guarantees (`T-8246-BALANCE-PRESERVED`, `T-8246-SAME-TX-CREATE-DESTROY`, `T-8246-NO-STATE-GAS-REFUND`, `T-8246-ETH-CONSERVATION`) and mutation kill-line `M-8246-1`.
4. **`Glamsterdam/Gas/Spec.lean`**: Coupled gas guarantees (`EIP-8037`, `8038`, `2780`, `7778`): `T-8037-CHARGE-GAS-SOUND`, `T-8037-RESERVOIR-ROUNDTRIP`, `T-8037-CREATE-ORDER`, `T-7778-NO-REFUND`, `T-7778-8037-DUAL-CAP`, `T-2780-INTRINSIC-SPLIT`, `T-8038-2780-WARM-COLD`, and mutation kill-lines `M-8037-1`, `M-7778-1`.
5. **`Glamsterdam/Gloas7732/Spec.lean`**: `EIP-7732` (+ `EIP-8282`) consensus state transition guarantees (`T-7732-SLASHED-NO-RESURRECTION`, explicit counterexample proof for `F-7732-SLASHED-PAYMENT-RESURRECTION` in `v1.7.0-beta.4`, `T-7732-BUILDER-SOLVENCY`, `T-7732-EXIT-SAFETY`, `T-7732-QUORUM-NO-DOUBLE-COUNT`, `T-7732-DEFERRED-EXEC-EQUIV`, `T-7732-FRAME`, and `T-8282-7732-QUEUE-SAFETY`).

## Quick Verification

```bash
make check
```
