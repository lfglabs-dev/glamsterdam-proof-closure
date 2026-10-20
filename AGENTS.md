# AGENTS.md: Architectural Charter (`glamsterdam-proof-closure` x `turbo-lean`)

## 1. Symbiosis and Architectural Roles

`glamsterdam-proof-closure` is the unified Lean 4.31 formal verification monorepo for the Ethereum Glamsterdam upgrade audits, built on top of `turbo-lean` and `lean-native`:

- **`Glamsterdam.Common` (Shared Execution Layer Core and Layer I Meta-Specs)**:
  Models the 16 shared Execution Layer functions (`State`, `Account`, `TransactionEnvironment`, `Evm`, `Message`, journal checkpoints `begin_transaction` / `commit_transaction` / `rollback_transaction`, `move_ether`, `clear_account_preserving_balance`, `charge_gas`, `incorporate_child_on_success`, `incorporate_child_on_error`, `process_create_message`, `process_message`, `execute_transaction`, `apply_body`) and provides reusable Layer I algebraic combinators (`MetaGateSpec`, `MetaAlgorithmSpec`, `ObservationalProj`, `FrameInvariant`, `WitnessRefuter`).
- **`Glamsterdam.Eip8246` (EIP-8246 Clear Destroyed Account Without Balance Wipe)**:
  Proves 1-to-1 ETH conservation across the EL transition, balance preservation on end-of-tx `clear_account_preserving_balance`, same-tx `CREATE` + `SELFDESTRUCT` storage destruction, and absence of state-gas refunds under `8246 + 8037`.
- **`Glamsterdam.Gas` (EIP-8037, EIP-8038, EIP-2780, EIP-7778 Coupled Gas Model)**:
  Proves two-leg `charge_gas` soundness (`gas_left` + `state_gas_reservoir`), 100% reservoir round-trip across child calls and reverts, `CREATE` / `CREATE2` state-gas ordering before the `63/64` cap, zero refund credits (`EIP-7778`), dual block gas accounting (`max(tx_regular, tx_state)` vs receipt gas), and `8038 + 2780` access-gas bounds.
- **`Glamsterdam.Gloas7732` (EIP-7732 ePBS Consensus Specs + EIP-8282 Queue Closure)**:
  Proves the `EIP-7732` payment lifecycle in `specs/gloas/beacon-chain.md` and `specs/gloas/fork.md` (with `fork-choice.md` and P2P out of scope), including the fix for `F-7732-SLASHED-PAYMENT-RESURRECTION`, builder balance solvency, builder exit safety, quorum anti-double-counting on target equivocation, deferred execution equivalence (`process_block` vs `process_execution_payload`), the non-interference Frame Theorem (`T-7732-FRAME`), and `EIP-8282 -> EIP-7732` deposit/exit queue safety.

```
Agent / CLI / MCP -> Stage 0: Cone & CAS Filter (`turbo-lean` + C-ABI `Glamsterdam`)
                  -> Stage 1: Non-Vacuity & Mutant Kill-Line Gate (`MetaGateSpec` / `WitnessRefuter`)
                  -> Stage 2: Speculative Tactic Racing & Warm Zygote Replay (`ZygoteWorker`)
                  -> Stage 3: In-Kernel Axiom & Metadata Pinning Gate (`turbo-lean ci-verify` + `audit_metadata.py`)
```

---

## 2. Five Non-Negotiable Engineering Rules

1. **Zero Model-Code Gap via Source-Map Pinning and Direct C-ABI (`@[export]`)**:
   Every Lean definition in `Glamsterdam/` maps line-by-line to a frozen upstream commit in `audit/source-map.yaml` (`ethereum/execution-specs` at `16898000911c1e3caa57be08509536c10ae92d3e`, `ethereum/consensus-specs` at `aa16bb4c156184e9548a997d53efaf2a228a6304`, `ethereum/EIPs` at `ed9b712640c1646dfda7ccceca2e0fd936b6472f`). Executable decision gates export C-ABI symbols (`@[inline, export ...]`) so external harnesses can invoke the verified Lean spec directly.

2. **Two-Layer Specification Compression (`Layer I` Meta-Specs vs. `Layer II` Corollaries <= 3 Lines)**:
   - **Layer I (Universal Meta-Specifications and Combinators)**: Structural reasoning lives in `Glamsterdam/Common/MetaSpec.lean` (`MetaGateSpec`, `MetaAlgorithmSpec`, `ObservationalProj`, `FrameInvariant`, `WitnessRefuter`).
   - **Layer II (Declarative Corollaries)**: Concrete EIP guarantees in `Eip8246/`, `Gas/`, and `Gloas7732/` are instantiated as `MetaGateSpec` / `FrameInvariant` bundles or corollaries of at most 3 lines discharging through Layer I combinators.

3. **Non-Vacuity and Mutation Kill-Lines (`WitnessRefuter`)**:
   Every guarantee must provide both a positive witness (`posWitness`) and a negative witness (`negWitness`) via `MetaGateSpec`, plus an explicit mutation kill-line (`WitnessRefuter`) proving that a 1-line bug in the transition function violates the theorem statement (including the real upstream bug `F-7732-SLASHED-PAYMENT-RESURRECTION`).

4. **Mathlib4 Algebraic Proof Style and Zero `sorryAx`**:
   Proofs follow concise algebraic idioms (`split <;> simp_all`, `simpa`, `omega`, `rfl`). Verbose `cases <;> cases` cascades, `sorryAx`, `native_decide`, and custom `axiom` declarations are forbidden and rejected by `turbo-lean ci-verify`.

5. **Strict Audit Metadata Discipline**:
   `audit/guarantees.yaml`, `audit/assumptions.yaml`, `audit/exclusions.yaml`, and `audit/source-map.yaml` must stay 100% synchronized with the Lean theorem declarations. Always run `make check` before opening or updating a pull request.

---

## 3. Repository Layout and Verification Entrypoints

- **Layer I Combinators**: [`Glamsterdam/Common/MetaSpec.lean`](Glamsterdam/Common/MetaSpec.lean)
- **Shared EL Core (16 Functions)**: [`Glamsterdam/Common/ElCore.lean`](Glamsterdam/Common/ElCore.lean)
- **Audit 1 (`EIP-8246`)**: [`Glamsterdam/Eip8246/Spec.lean`](Glamsterdam/Eip8246/Spec.lean)
- **Audit 2 (`EIP-8037`, `8038`, `2780`, `7778`)**: [`Glamsterdam/Gas/Spec.lean`](Glamsterdam/Gas/Spec.lean)
- **Audit 3 (`EIP-7732` + `EIP-8282`)**: [`Glamsterdam/Gloas7732/Spec.lean`](Glamsterdam/Gloas7732/Spec.lean)
- **Audit Metadata and Findings**: [`audit/guarantees.yaml`](audit/guarantees.yaml), [`audit/source-map.yaml`](audit/source-map.yaml), [`audit/findings/F-7732-SLASHED-PAYMENT-RESURRECTION.md`](audit/findings/F-7732-SLASHED-PAYMENT-RESURRECTION.md)
- **Reproducible `pyspec` Tests**: [`tests/pyspec/test_slashed_proposer_payment_resurrection.py`](tests/pyspec/test_slashed_proposer_payment_resurrection.py)

## 4. Local Verification Commands

```bash
make prove         # Compile all Lean 4.31 modules
make turbo-verify  # Run turbo-lean ci-verify and audit-spec across all modules
make audit-check   # Validate audit/*.yaml against Lean theorem declarations
make check         # Full gate (prove + turbo-verify + audit-check)
```
