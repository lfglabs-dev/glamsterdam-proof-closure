# Official Gloas reference suite

Run the command below from the proof checkout, with the pinned Lean toolchain,
a C compiler, GNU tar, and the v1.7.0-beta.4 PySpec checkout prepared as in
[CI](../../.github/workflows/builder-payment-vectors.yml).

```sh
/path/to/consensus-specs/.venv/bin/python tests/reference_vectors/check_payments.py /path/to/archives payment-results.json
```

The archive directory contains all four original release files. The runner verifies
their SHA-256 digests and reconciles case directories, manifests and payloads.
The reference denominator includes every case published under Gloas in minimal,
mainnet and general, including Gloas outputs of inherited tests. General publishes
zero such cases. The 1,472 Gloas cases in comptests are reported separately.
Cases published only for other forks and Python unit functions without fixtures
are outside the denominator.

The CI artifact lists reference and compliance cases, dispositions, model
dependencies, revisions, and pinned pytest generator candidates. It uses the
upstream plugin's manifest inference during collection. Where multiple Python tests
infer the same path, all candidates are listed. The artifact separately names
Gloas-directory Python-only functions. For example, the phase0 attestation
test at_max_inclusion_slot contributes published Gloas cases, while the Gloas
unit test exit_churn_approximately_double_consolidation has no vector.

The compiled Lean adapter computes payment quorum from raw validator inputs.
Payment processing replaces both payment queues. Exit and top-up processing
replace the builder registry. The SSZ adapter encodes these replacements on the
pre-state and compares the complete resulting BeaconState bytes against the
official post-state. It does not copy any fields from the expected state.
New registrations use the Lean signing root and registry transition. The pinned blst library checks compressed points, subgroup membership, infinity and the BLS signature. Set GLOAS_BLST_DIR to a built checkout of blst v0.3.16 at e7f90de551e8df682f3cc99067d204d8b90d27ad, or build it in .blst as in CI.
Negative controls swap the payment halves, drop a registry update, or verify a valid builder signature with a different genesis fork version.

The baseline pins the exact case-ID set for each disposition; any coverage change
requires review. CI also fails on digest or generator mismatches, missing cases,
duplicate manifests, and failed supported cases. A green inventory run does not
imply that every reference case passed.

## Static SSZ cases

For the pinned Gloas `ssz_static` corpus, this runner implements the binary
acceptance rule in the upstream `tests/formats/ssz_static/core.md`. Python reads
the type declarations for the selected preset, decompresses the official bytes,
and reads the expected root. It performs no SSZ decoding or tree hashing for
these cases. Lean checks field widths, bitlist terminators, collection limits
and variable offsets, rebuilds the serialization and compares it byte-for-byte.
Lean builds the bounded or progressive Merkle tree and mixes in lengths or
active-field masks. Lean computes SHA-256 for each pair of chunks.

The official format allows the binary round trip plus the expected tree root
for a binary-only codec. The runner does not claim to implement the optional
YAML value codec or complete beacon-state transitions through these tests.
Local malformed-wire and length-mix-in controls are separate from the official
denominator.

Payload-attestation replay uses the official fixture's fork configuration.
Lean checks the parent root and previous-slot rule, selects the PTC window and
signers, and chooses the fork version for the attested epoch. The native BLS
primitive verifies the resulting aggregate signature under the PTC domain.
The valid operation has no state writes, so its complete pre-state encoding
must equal the published post-state. Cases without a post-state must be rejected.
These cases exercise payload-timeliness attestations. Ordinary beacon
attestations have additional committee, participation and reward transitions.

## ePBS claim audit

The three additional operation handlers run 48 parent-payload, 40 bid, and 127 ordinary attestation cases. The report distinguishes a complete hybrid post-state from a Lean rejection and a Python rejection. A Python rejection may occur before Lean runs, or after Lean accepts a builder's coverage check. Each bid row records which happened.

| Handler | Computed by Lean | Supplied by pinned Python |
| --- | --- | --- |
| Parent payload | Full/empty hash comparison, request commitment equality, request count limits, payment-window index, clearing an entry and appending its withdrawal or settling an older bid | SSZ roots, nested execution requests after settlement, availability bit and latest hash |
| Execution payload bid | Outstanding obligations in both queues, the coverage guard, the pending entry for a positive bid | Builder eligibility and version, signature, block context and proposer index, latest bid assignment |
| Ordinary attestation | Same-slot eligibility, source/target/head flags, prior participation, payment index, exact weight and participation updates | Committee assignment, signature, historical roots, reward calculation and proposer balance update |
| Surrounding cases | Selected builder debits, slashing's pending-payment projection, fork-slot availability | Withdrawal selection, validity of slashing inputs, registry onboarding, unrelated state fields |

For multi-block fixtures the report identifies the operations present in valid Gloas blocks. The final block of a rejected sequence is listed separately because the body cannot establish how far execution proceeded. All valid multi-block histories that record a positive bid and have at least two Gloas blocks are replayed with the compiled payment operations. Each successful row records checked intermediate operations, complete signed-block execution and official final-state equality. Screening alone adds no whole-chain passes. Supplemental sequences and mutation checks have their own report section.
