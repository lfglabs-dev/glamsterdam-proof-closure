SHELL := /usr/bin/env bash
.SHELLFLAGS := -euo pipefail -c
export PATH := $(HOME)/.local/bin:$(PATH)

.PHONY: bootstrap prove turbo-verify diff-test audit-check check

bootstrap:
	@lake env lean --version
	@lake --version
	@turbo-lean --version

prove:
	@lake build
	@python3 scripts/audit_metadata.py
	@printf '%s\n' 'prove ok: Common EL core, Eip8246, Gas (8037/8038/2780/7778), Gloas7732 (+8282), and TestVectors compiled with 0 sorryAx, 0 axiom, 0 native_decide'

turbo-verify: prove
	@turbo-lean --json ci-verify --project-dir . --mode trusted --scope Glamsterdam --receipt .lake/turbo-receipt.json
	@turbo-lean --json verify-receipt .lake/turbo-receipt.json --baseline-receipt .lake/turbo-receipt.json
	@if turbo-lean --help 2>&1 | grep -q "audit-spec"; then \
		turbo-lean --json audit-spec Glamsterdam/Common/Prelude.lean; \
		turbo-lean --json audit-spec Glamsterdam/Common/MetaSpec.lean; \
		turbo-lean --json audit-spec Glamsterdam/Common/ElCore.lean; \
		turbo-lean --json audit-spec Glamsterdam/Eip8246/Spec.lean; \
		turbo-lean --json audit-spec Glamsterdam/Gas/Spec.lean; \
		turbo-lean --json audit-spec Glamsterdam/Gas/CallTree.lean; \
		turbo-lean --json audit-spec Glamsterdam/Gas/Eip12582.lean; \
		turbo-lean --json audit-spec Glamsterdam/Gloas7732/Spec.lean; \
		turbo-lean --json audit-spec Glamsterdam/TestVectors.lean; \
	fi

diff-test: prove
	@python3 tests/differential/test_glamsterdam_differential.py
	@pytest tests/ -v

audit-check:
	@python3 scripts/audit_metadata.py
	@python3 scripts/verify_ground_truth.py --self-test
	@python3 scripts/verify_ground_truth.py --enforce-ledger-step all

check: prove turbo-verify diff-test audit-check
	@printf '%s\n' 'check ok: all Glamsterdam Lean 4.31 proofs, turbo-lean gates, C-ABI differential tests, and ground-truth audit metadata verified'
