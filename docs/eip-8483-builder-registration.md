# EIP-8483 builder registration

At dequeue, resolve the request's public key in the current ordered builder registry and check the execution address. An authorized request sets that key's material; every other key retains its previous value. An absent key or wrong sender leaves the whole mapping unchanged.

| Property | Lean declaration in Glamsterdam.Eip8483.Spec |
| --- | --- |
| Current owner can register and overwrite | `authorized_write` |
| Unknown key or unauthorized sender has no effect | `unauthorized_unchanged` |
| Other registrations survive every request | `other_key_unchanged` |
| A different builder occupying the reused index retains its own registration | `delayed_registration_after_reuse` |
| Resolving a cached index to its new occupant violates isolation even if both use the same execution address | `cachedIndexRefuter` |

The executable examples register Alice, replace her at the same index with Bob, and check Bob's existing material. A separate example re-registers Alice's public key under a new address. Her old material persists, the old owner cannot overwrite it, and the new owner can.

The model reuses the Gloas Builder record. It represents the SSZ registration list by its per-key lookup, assuming unique entries and room for an authorized append. Keys, addresses and public material are opaque equality-preserving values. The result holds across arbitrary changes before processing; it assumes a decoded request with authentic source address. It does not verify the EL contract, queue delivery, registry replacement eligibility, or migration policy.

Source: ethereum/EIPs draft PR 12609, commit 20e8d373921053e61cc82cbb9cdf2311753679fd, EIPS/eip-8483.md, process_pq_builder_registration_request. Gloas builder baseline: ethereum/consensus-specs aa16bb4c156184e9548a997d53efaf2a228a6304.
