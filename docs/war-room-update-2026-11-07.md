# Glamsterdam war-room update — 2026-11-07

**Author:** `agent:opencode` (synthesis, not an EF statement)
**Scope:** reconcile the 2026-11-06 upstream status with our pinned proof closure, refresh the repo-side record, and fix Monday’s action list.
**Pinned spec:** unchanged — `ethereum/execution-specs@16898000911c1e3caa57be08509536c10ae92d3e` (`Amsterdam D0`), plus `EIPs#12581` / `#12582` variants.

## 1. What changed upstream on 2026-11-06

Verified from the EF post [`blog.ethereum.org/2026/11/06/glamsterdam-8037-8038`](https://blog.ethereum.org/2026/11/06/glamsterdam-8037-8038) (Marius van der Wijden) and the linked [`ethereum/glamsterdam-gas-invariants`](https://github.com/ethereum/glamsterdam-gas-invariants) repo:

- ACD **delayed the Glamsterdam hardfork** and **did not fork Hoodi**. Mainnet is unscheduled. Hegota is unaffected.
- EF published **8 broken gas invariants** for auditors, with red flags and fixes, and a call for ecosystem feedback at `glamsterdam@ethereum.org`.
- Four ACD options are on the table: (1) ignore, (2) add time, (3) change the EIPs, (4) pull the EIPs.
- Related artefacts: [ChainSecurity post](https://www.chainsecurity.com/blog/glamsterdam-gas/index.html), [EF repricing tool](https://rahul-kothari.github.io/repricing/), [`ethereum/8037-findings`](https://github.com/ethereum/8037-findings).
- Signal reports add: Hubert (ChainSecurity) says more OP-Stack chains are affected (World, Base, Ink) and the list is incomplete; honest `eth_estimateGas` submitters can accidentally trigger the attack; Rahul reports OP Sepolia upgrade on Monday and Uniswap/Shiba fixes by January.

## 2. Reconciliation with our records

| Record | Status | Correction |
| :--- | :--- | :--- |
| “Hoodi activated 26 Oct.” in the Hindsight Glamsterdam page | **SUPERSEDED 2026-11-07** | Hoodi was not forked. Do not repeat the 26 Oct. activation claim. |
| Internal Lean closure (26 Oct., `0 sorryAx`, `0 axiom`, `100% non_vacuous_and_tight`) | Still valid | The pinned spec did not change; `audit/guarantees.yaml` remains the canonical 60-guarantee ledger. |
| “41 guarantees / 75 shards” in older context | Stale | Use `audit/guarantees.yaml` (60) and `audit/findings/GLAMSTERDAM-AUDIT-REPORT.md` v3 (60/60 guarantees, 10 verified findings) for repo-side counts. The 80/29/3 figure is the external `8037-findings` tracker, a different unit. |
| EIP-8246 still in the Glamsterdam EL set | Open | Thomas’s 1 Nov. note proposed replacing it with EIP-7708 per-wei logs (lead Paweł). No sign-off surfaced. Do not close or expand Track 2 until Paweł answers. |
| External findings count | Moved | EF + Dedaub + ChainSecurity consolidated to roughly **6 HIGH / 66 MEDIUM / 51+ LOW** at 2026-11-07. Treat our 3 High / 23 Medium / 54 Low as a floor snapshot from 25 Oct., not the current total. |

## 3. Re-scope of the three tracks

1. **Track 1 — Gas 2D (8037/8038/2780/7778): highest value now.**
   EF’s 8 invariants are exactly the surface our closure already models. Publish the theorem-by-theorem map (`docs/ef-invariants-map.md`) and offer the estimator-safety lemma. This is the track where “we already did X, check it in the repo” is true and checkable.
2. **Track 3 — ePBS (7732/8282): one nudge, do not reopen.**
   The four Potuz invariants and the FIFO `P-SUBMIT-1` / `P-DRAIN-1` / `P-CONTROL-1` closure are done. Ask Potuz for a yes/no sign-off, not a new review cycle.
3. **Track 2 — EIP-8246: one question, no work.**
   Ask Paweł whether 8246 stays in the fork or is replaced by 7708 logging. Only then decide whether the `T-8246-*` guarantees remain in the delivery narrative.

## 4. Monday 2026-11-09 action list (timeboxed)

| # | Window | Action | Done when | Dependency |
| :--- | :--- | :--- | :--- | :--- |
| 1 | 09:00–09:30 | Send the TLP:AMBER note to Marius: EF delayed Hoodi, we already have the INV-1…8 map, link `docs/ef-invariants-map.md`, offer the estimator lemma and a 30-min walkthrough. | Message sent; one link + one ask. | None. |
| 2 | 09:30–11:30 | Draft `EstimatorSafety` spec: for an honest estimator that binary-searches on `gasleft()` deltas over `eth_call`, exhibit a trace where reservoir draw is missed when `tx.gas > 2^24`. Put the statement in `docs/estimator-safety-spec.md`; if it stabilises, open `Glamsterdam/Gas/Estimator.lean`. | Spec has a precise statement, witness, and failure condition. | Item 1 wording only. |
| 3 | 11:30–12:00 | Ask Paweł (one question): “Is 8246 still in the Glamsterdam EL set, or is it being replaced by 7708 per-wei logs? We need to know whether to keep the 8246 guarantees in the delivery.” | Answer or explicit pending. | None. |
| 4 | 14:00–15:00 | Ping Potuz / ePBS thread: the four invariants plus FIFO closure are kernel-checked; request a yes/no sign-off with theorem links. Do not propose new scope. | Sign-off requested with links. | None. |
| 5 | 15:00–17:00 | Send Fredrik a one-paragraph status: blog delta, Hoodi correction, INV map link, 8246 question, ePBS sign-off request. Update `kp-glamsterdam-eip-audits` and `kp-business-verity-audits` with the same delta. | Fredrik message sent; both Hindsight pages refreshed. | Items 1–4. |
| 6 | 17:00–17:30 | Reconcile external findings counts (EF/Dedaub/ChainSecurity vs our 25 Oct. snapshot) in a short `docs/findings-reconciliation.md`; label each row as in-model, client-only, or out-of-scope. | Table exists; no claim that the 25 Oct. count is current. | None. |

**Do not do on Monday:** re-audit `D0`; claim Hoodi activation; open a new 8246 workstream before Paweł answers; describe the 25 Oct. findings count as the current total.

## 5. Repo changes in this update

- Added `docs/ef-invariants-map.md` — EF INV-1…8 to Lean theorem map, with explicit gaps.
- Added this file — upstream delta, reconciliation table, Monday list.
- Added a status note to `README.md` and `audit/findings/GLAMSTERDAM-AUDIT-REPORT.md`.
- No Lean statements or pinned sources changed. `make check` remains the verification entrypoint.
