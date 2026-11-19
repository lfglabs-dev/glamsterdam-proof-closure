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
New builder registrations requiring BLS verification are explicitly unsupported.
Negative controls swap the payment halves or drop a registry update.

The baseline pins the exact case-ID set for each disposition; any coverage change
requires review. CI also fails on digest or generator mismatches, missing cases,
duplicate manifests, and failed supported cases. A green inventory run does not
imply that every reference case passed.
