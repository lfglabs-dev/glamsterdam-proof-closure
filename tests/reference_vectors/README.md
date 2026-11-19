# Official Gloas builder-payment vectors

The GitHub Actions job **Official Gloas builder-payment vectors** runs the entire
`gloas/epoch_processing/builder_pending_payments` handler from the official
minimal and mainnet v1.7.0-beta.4 archives. Its JSON artifact lists each case,
the archive digests, the compared fields and the revisions.

The runner decodes the handler's immediate pre/post BeaconStates using the
pinned PySpec. It passes the pre-state active balance, preset size, ordered
two-epoch payment window and existing withdrawal queue across the C ABI.
Lean computes the quorum and calls the audited payment transition. The runner
compares every entry and field of both output queues with the fixture.
The optional pre_epoch and post_epoch files span other epoch operations.

To rerun, use the decoder checkout, archive URLs and setup commands in
[the workflow](../../.github/workflows/builder-payment-vectors.yml). From the
proof checkout, with the pinned Lean toolchain and a C compiler on PATH, run:

```sh
/path/to/consensus-specs/.venv/bin/python tests/reference_vectors/check_payments.py /path/to/archives payment-results.json
```

The archive directory must contain both original release files. Missing,
unrecognized or mismatching cases in the selected handler fail the run.
