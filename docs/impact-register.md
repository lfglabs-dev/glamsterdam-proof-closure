# Glamsterdam Impact Register

**Status:** draft template, refreshed 2026-11-11. Rows land here only after the evidence gate below.
**Companion:** `docs/spec-cards.md` (C1–C12), `docs/estimator-safety-spec.md`, `docs/simplification-plan.md`.

## Evidence gate

A row enters the main table only if it has:

1. **Coordinates.** `chain`, pinned `block`, resolved implementation `address`, `bytecode_hash` (EIP-1967 slot resolved, not the proxy shell), `selector`, `fork_variant ∈ {D0, D13R, D13A}`.
2. **Source.** `source_url` + `source_line` (or verified Sourcify path), and the exact guard/line that assumes the invariant.
3. **Divergence.** A dual execution at the same block: Osaka succeeds, Amsterdam fails or leaves permanent state (or the inverse), with `(tx.gas, gasLeft, stateGasLeft)` before/after.
4. **Reachability.** An untrusted-caller path to the sink; if reservoir-dependent, an argument why `tx.gas > 2^24` is producible by an attacker or an honest estimator.
5. **Theorem.** A card ID C1–C12 plus an existing theorem, or an explicit `GAP` with a ≤30-line counterexample trace.

Inferred or pattern-only rows go to the appendix, never the main table. An external report with exact coordinates and numbers goes in the external-reports section, labelled “external, rerun pending”; it is not promoted to the main table until we reproduce it. No public 0-day disclosure; sensitive rows are marked `EMBARGOED` and shared only with EF.

## External address-level reports (not yet independently rerun)

| ID | Card | Fork | Chain | Contract / component | Invariant | Evidence | Impact | Confidence |
|---|---|---|---|---|---|---|---|---|
| UNI-V4-01 | C4/C5/C6 + C13 candidate | D0 | mainnet; also Base/Unichain | Uniswap v4 `PositionManager` `0xbD216513d74C8cf14cf4747E6AaA6420FF64ee9e`; `unsubscribe` / subscribed transfer; `notifyUnsubscribe{gas: 150_000}` | INV-4/5/6 + proposed fixed-budget determinism | Uniswap public report (Daniel Gretzke); mainnet-fork Amsterdam: 172,044 gas at `tx.gas ≤ 2^24` (OOG caught, tx succeeds), 255,543 gas at 16.9M (callback succeeds), `eth_estimateGas` = 169,842 (failing path); mechanism theorem `Glamsterdam.Gas.Spec.t_8037_c13_fixed_budget_subcall_tx_gas_dependent` | Sender/bundler chooses whether the callback runs; subscriber state goes stale; forcing success shows ~65× higher maximum fee | confirmed mechanism; external address repro (`GAP`: independent fork rerun pending) |

## Main table — mechanism-level confirmations

These rows are confirmed by the EF invariant text and the ChainSecurity analysis; they are **not** a claim that a specific deployed address is exploitable. Address-level rows from L1/L2 are appended below once they pass the gate.

| ID | Card | Fork | Chain | Contract / component | Invariant | Evidence | Impact | Confidence |
|---|---|---|---|---|---|---|---|---|
| EF-INV4-01 | C4 | D0 | all | first-time recipient; oracle callback; bridge destination gas | INV-4 | `ethereum/glamsterdam-gas-invariants` `invariants/inv-4.md`; ChainSecurity §4 | fixed budget 65k can need >150k; caught failure becomes permanent | confirmed mechanism |
| EF-INV7-01 | C7 | D0 | all | `transfer`/`send` to a contract `receive`; relayer reserve | INV-7 | `invariants/inv-7.md`; ChainSecurity §1 | 2,300 stipend cannot create a 110,020 slot; reserve of 40k no longer covers the post-call write | confirmed mechanism |
| CS-INV1-01 | C1 | D0 | all | failure handler that writes a fresh slot and marks done | INV-1 | ChainSecurity §1 | reservoir pays 97,920 state gas; handler completes where Osaka reverted | confirmed mechanism |
| CS-INV2-01 | C2/C8 | D0 | all | lock/flag `0 → 1 → 0` around a call | INV-2 | ChainSecurity §2 | clear refills up to 97,920 execution gas; B1/B2 gas checks can be bypassed | confirmed mechanism |
| CS-INV3-01 | C3 | D0 | all | `C → D → E`, `D` reverts after creating state | INV-3 | ChainSecurity §3 | `D` returns unused gas plus refunded state creation; outer check sees more gas | confirmed mechanism |
| EF-INV8-01 | C12 | D0 | all | 7702 delegate with unprotected `initialize` | INV-8 | `invariants/inv-8.md` | mined status-0 tx leaves a valid authorization; attacker reuses it and calls `initialize` | confirmed mechanism; full replay trace `GAP` |
| EF-SCAN-01 | C4/C7 | D0 | all | EF Sourcify corpus | INV-4, INV-7 | repo README: “most findings reference INV-4 and INV-7” | EF has address-level findings; not public yet | confirmed by EF, addresses withheld |
| RPC-EST-01 | C5/C6 | D0 | off-chain | ERC-4337 `EntryPoint.innerHandleOp` / `eth_estimateUserOperationGas` | INV-5, INV-6 | Pimlico/EF call 29 Oct (relayed); ChainSecurity 4 Nov; `Glamsterdam.Gas.Spec.estimator_unsound_above_2pow24` & `allocation_zero_reservoir_below_2pow24` (`docs/estimator-safety-spec.md`) | Pimlico reports real Sepolia user flows broke; their workaround caps simulation at 16,777,216, excluding state-heavy ops | confirmed budget condition & off-chain incident; client RPC trace `GAP` |

Address-level rows (L1/L2) are appended here only after the evidence gate; the table above is the invariant-level baseline that does not depend on a single deployment.

## Appendix A — inferred or pattern-only

| ID | Card | Chain | Component | Why inferred | Next test |
|---|---|---|---|---|---|
| HYP-OP-01 | C1/C6/C7 | OP Stack | `CrossDomainMessenger` / `OptimismPortal` failed-message marking | ChainSecurity says more OP-Stack chains are affected (World/Base/Ink), but the public list is incomplete; no address-level trace yet. OP testnet upgraded successfully on 11 Nov; EF has a comms contact. | use the OP-Stack contact; pin a failed relay on OP Sepolia/Base; replay Osaka vs Amsterdam; show permanent failed marker |
| HYP-4337-01 | C5/C6 | all | ERC-4337 `EntryPoint` v0.6/0.7/0.8 | Pimlico report is off-chain; no public contract trace | run `eth_estimateUserOperationGas` at a cap above/below 2^24 on an Amsterdam node |
| HYP-DEX-01 | C2/C8 | mainnet | DEX/lending lock flags | pattern is common, but no specific contract has been run | grep verified source for `0 → 1 → 0` around `call`; dual-execute |
| HYP-ORACLE-01 | C4 | mainnet | oracle callback budgets | EF flags first-time recipients; no specific feed tested | pick a feed with a fresh consumer slot; force callback OOG |

## Candidate classes to check (not claims)

- **ERC-4337 EntryPoint v0.6/0.7/0.8** — `innerHandleOp` bills by `gasleft()` deltas; reservoir invisible above `2^24`. Hits C1/C4/C5/C6/C7 at once.
- **OP-Stack `CrossDomainMessenger` / `OptimismPortal`** — `SafeCall.callWithMinGas`, failed-message marking; 1/64 retention + reservoir spill. Hits C1/C6/C7.
- **7702 `setup` / `initialize`** — mined-but-rolled-back delegation; replay. Card C12 is a GAP.
- **DEX / lending lock flags** — `0 → 1 → 0` around an external call; refund at clear. C2/C8.
- **Oracles with fixed heartbeat budgets** — Chainlink `fulfill` / callback gas caps; C4.
- **Bridges / L1 messengers** — fixed `gasLimit` on `receive`; C4/C6.

## False-positive triage (11 Nov)

- EF chat estimates ~80% of `8037-findings` entries are likely AI false positives. Do not use the raw count as blast radius.
- Known false-positive classes: changeable EOA gas limits; “underflow” with no state-changing operation between the gas reads; Uniswap Permit2’s 5,000-gas cap (works with an access list).
- Banteg’s “200k contracts broken” is unverified. The arachnid CREATE2 factory is already on mainnet, is not deployable on new chains, and EIP-7997 enshrines it. Treat this as a comms claim until a reproducible row exists.
- `ethereum/8037-findings` is referenced publicly with PR #343, but the repo API returns 404 to an unauthenticated request; treat it as private/inaccessible and do not cite entry counts as evidence.

## Open questions for EF

1. Does the client expose `state_gas_left` to `eth_call`, or is the estimator expected to simulate with the reservoir disabled?
2. Is 8246 still in scope, or superseded by 7708 per-wei logs?
3. Which of C1–C12 does EF want as the canonical review surface for the next ACD call?
4. Will EF adopt a deterministic fixed-budget-call rule (Uniswap v4 case), or document the `tx.gas`-dependent outcome as an accepted break?
