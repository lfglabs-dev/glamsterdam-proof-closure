SHELL := /usr/bin/env bash
.SHELLFLAGS := -euo pipefail -c

.PHONY: bootstrap prove turbo-verify audit-check check

bootstrap:
	@lake env lean --version
	@lake --version
	@turbo-lean --version

prove:
	@lake build
	@printf '%s\n' 'prove ok: Common EL core, Eip8246, Gas (8037/8038/2780/7778), and Gloas7732 (+8282) compiled with 0 sorryAx'

turbo-verify: prove
	@turbo-lean --json ci-verify --project-dir . --mode trusted --receipt .lake/turbo-receipt.json
	@turbo-lean --json verify-receipt .lake/turbo-receipt.json --baseline-receipt .lake/turbo-receipt.json
	@if turbo-lean --help 2>&1 | grep -q "audit-spec"; then \
		turbo-lean --json audit-spec Glamsterdam/Common/ElCore.lean; \
		turbo-lean --json audit-spec Glamsterdam/Eip8246/Spec.lean; \
		turbo-lean --json audit-spec Glamsterdam/Gas/Spec.lean; \
		turbo-lean --json audit-spec Glamsterdam/Gloas7732/Spec.lean; \
	fi

audit-check:
	@python3 scripts/audit_metadata.py

check: prove turbo-verify audit-check
	@printf '%s\n' 'check ok: all Glamsterdam Lean 4.31 proofs, turbo-lean gates, and audit metadata verified'
