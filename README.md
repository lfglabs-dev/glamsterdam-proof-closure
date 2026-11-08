# Glamsterdam Proof Closure

Lean 4.31 formal verification monorepo for the Ethereum Glamsterdam upgrade audits, verified with [`turbo-lean`](https://github.com/Th0rgal/turbo-lean) (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`).

## Status (2026-11-07)

- Upstream ACD **delayed the Glamsterdam hardfork and did not fork Hoodi** ([EF post, 2026-11-06](https://blog.ethereum.org/2026/11/06/glamsterdam-8037-8038)). The pinned spec and the internal closure in this repo are unchanged; external lead sign-off is pending.
- EF published eight gas invariants for auditors. The theorem-by-theorem mapping is in [`docs/ef-invariants-map.md`](docs/ef-invariants-map.md), including the residual gaps (notably the off-chain `eth_estimateGas` estimator and INV-8 replay).
- **12 Spec Cards** — one auditable statement per invariant plus 8246/ePBS/8282/7702: [`docs/spec-cards.md`](docs/spec-cards.md).
- **Reviewer path (20 min):** [`docs/README-spec-review.md`](docs/README-spec-review.md); simplification plan and trusted core: [`docs/simplification-plan.md`](docs/simplification-plan.md).
- **Impact register** (confirmed mechanisms vs inferred hypotheses): [`docs/impact-register.md`](docs/impact-register.md); estimator hazard: [`docs/estimator-safety-spec.md`](docs/estimator-safety-spec.md).
- **EF one-pager:** [`docs/ef-report.md`](docs/ef-report.md); **6-week remediation plan:** [`docs/remediation-plan.md`](docs/remediation-plan.md).
- War-room delta and the Monday 2026-11-09 action list: [`docs/war-room-update-2026-11-07.md`](docs/war-room-update-2026-11-07.md).

## Pinned Upstream Targets

| Upstream Repository | Pinned Commit / Tag | Scope |
|---|---|---|
| `ethereum/execution-specs` | `16898000911c1e3caa57be08509536c10ae92d3e` (Oct 20, 2026) | `src/ethereum/forks/amsterdam/` (`EIP-8246`, `8037`, `8038`, `2780`, `7778`) |
| `ethereum/consensus-specs` | `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`, Oct 19, 2026) | `specs/gloas/beacon-chain.md` and `specs/gloas/fork.md` (`EIP-7732`, `EIP-8282`) |
| `ethereum/EIPs` | `ed9b712640c1646dfda7ccceca2e0fd936b6472f` (Oct 20, 2026) | Normative EIP specifications (`8246`, `8037`, `8038`, `2780`, `7778`, `7732`, `8282`) |
| `lfglabs-dev/eip-8282-proof-closure` | `303a07d112d8aa51178c5d99c8e185b18bfddba7` | `EIP-8282` predeploy guarantees (`P-SUBMIT-1`, `P-DRAIN-1`, `P-CONTROL-1`) |

## Architecture

1. **`Glamsterdam/Common/Prelude.lean`**: State-preserving `Result ε σ α` and `SpecM σ ε α` monad, checked/saturating arithmetic helpers (`checkedSub?`, `saturatingSub`, `checkedAddU64?`, `ceil32`), and Layer-0b `@[simp]` equation lemmas.
2. **`Glamsterdam/Common/MetaSpec.lean`**: Meta-specification combinators (`Costed`, `MetaGateSpec`, `MetaAlgorithmSpec`, `FrameInvariant`, `ExactDeltaSpec`, `WitnessRefuter`, `MutantKillBundle`, `NonVacuousSpec`, `OutcomePartitionSpec`, `AccountingBoundarySpec`, `OrderIndependence`).
3. **`Glamsterdam/Common/ElCore.lean`**: Full-fidelity Execution Layer transcription (`Account`, `PreState`, `BlockState`, `TransactionState`, `GasMeter`, state-journal snapshots/rollbacks, `modify_state` / `NoEmptyAccountLeaves` preservation across all `state_tracker.py` mutators, stateful BAL read-tracking transitions `read_account_tx` / `read_storage_tx`, 2D gas charging/spill/LIFO refund, and C-ABI exports).
4. **`Glamsterdam/Eip8246/Spec.lean`**: `EIP-8246` guarantees (`T-8246-BALANCE-PRESERVED`, `T-8246-SAME-TX-CREATE-DESTROY`, `T-8246-TX-STATE-CLEAR-EXACT`, `T-8246-SELFDESTRUCT-CONSERVATION`, `T-8246-NO-STATE-GAS-REFUND`, `T-8246-FEE-SETTLEMENT-CONSERVATION`, `T-8246-ETH-CONSERVATION`, `T-8246-BAL-PATCHED-SOUND`, `T-8246-STORAGE-CLEARS-RECORDED-IN-BAL`) and refuters (`M-8246-1`, `F-8246-BAL-STORAGE-CLEARS-IGNORED`, `F-8246-UNCHECKED-SYS-TX-DROPS-ACCOUNTS-TO-DELETE`).
5. **`Glamsterdam/Gas/Spec.lean`**: Coupled gas guarantees (`EIP-8037`, `8038`, `2780`, `7778`): `T-8037-CHARGE-GAS-SOUND`, `T-8037-RESERVOIR-ROUNDTRIP`, `T-8037-METER-RESERVOIR-ROUNDTRIP-REVERT`, `T-8037-SYS-TX-RESERVOIR-SOUND`, `T-8037-ALLOCATE-EVM-GAS-SOUND`, `T-7778-8037-DUAL-CAP`, `T-8038-2780-WARM-COLD`, `T-8037-7702-DELEGATION-INVARIANT-EQUIV`, and refuters (`M-8037-1`, `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS`, `F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE`, `F-2780-7928-SET-DELEGATION-OOG-OMITS-RECIPIENT-READ`).
6. **`Glamsterdam/Gas/CallTree.lean`**: Fork-parameterized compositional multi-frame EVM call-tree gas core (`FV-CORE`, `ForkSchedule`: `osaka`, `amsterdamD0`, `amsterdamD1`, `amsterdamD3`, `amsterdamD4`, `amsterdamD13`, `amsterdamD13R`, `amsterdamD13S`), `exec_sstore_frame` with mandatory `2300` sentry (`GAS_SSTORE_SENTRY`), `enter_child_frame` (`drain_state_gas_reservoir`), `exit_child_frame` (`incorporate_child`, `restore_state_gas`, `repay_state_gas_spill`, `repay_state_gas_spill_capped`), `settle_top_frame`, and 9 compositional compatibility & refill-variant theorems (`T-CALLTREE-SSTORE-SENTRY-EXCLUDES-RESERVOIR`, `T-CALLTREE-A1-FRAME-BOUND`, `T-CALLTREE-E1-FIXED-GRANT-STARVATION`, `T-CALLTREE-E3-M2-DIRTY-CLEAR-AND-D13R-BREAK`, `T-CALLTREE-D13R-NEW-T1-BAND`, `T-CALLTREE-E3-M3-REVERT-RESTORE-BAND`, `T-CALLTREE-E3-M4-SIBLING-AND-D13S-BREAK`, `T-CALLTREE-D13S-REOPENS-T2-CHILD-CLEAR`, `T-CALLTREE-D13S-FAILED-CREATE-STRANDS-GAS`).
7. **`Glamsterdam/Gloas7732/Spec.lean`**: First-principles `EIP-7732` (+ `EIP-8282`) consensus state transition guarantees (`T-7732-SINGLE-SETTLEMENT`, `T-7732-NO-ETH-MINTING`, `T-7732-PAYMENT-GUARANTEE`, `T-7732-QUORUM-NO-DOUBLE-COUNT`, `T-7732-QUORUM-WEIGHT-UNCONDITIONAL`, `T-7732-SAME-SLOT-UNBUNDLING`, `T-7732-SLASH-VALIDATOR-CLEARS-PAYMENTS`, `T-7732-SLASHED-NO-RESURRECTION`, `T-7732-BUILDER-SOLVENCY`, `T-7732-EXIT-SAFETY`, `T-7732-DEFERRED-EXEC-EQUIV`, `T-7732-FRAME`, `T-8282-7732-QUEUE-SAFETY`) and edge-case refuters (`F-7732-SLASHED-PAYMENT-RESURRECTION`, `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP`, `F-7732-FORK-ONBOARD-CROSS-CREDENTIAL`, `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH`, `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER`).
8. **`Glamsterdam/TestVectors.lean`** & **`tests/`**: Kernel-checked test vectors (`by decide` / `by rfl`), C-ABI differential testing directly against AST-extracted vendored upstream Python specifications (`pytest tests/ -v`), and `scripts/verify_ground_truth.py`.
9. **`audit/findings/GLAMSTERDAM-AUDIT-REPORT.md`**: Consolidated report of the 60 formal guarantees and 10 verified specification edge-case findings across CL (`7732/8282`) and EL (`8246`, `8037`, `8038`, `2780`, `7778`, and `FV-CORE` multi-frame gas semantics).

## Quick Verification

```bash
make check
```
