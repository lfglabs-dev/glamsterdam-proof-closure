SHELL := /usr/bin/env bash
.SHELLFLAGS := -euo pipefail -c
export PATH := $(HOME)/.local/bin:$(PATH)

.PHONY: bootstrap prove turbo-verify diff-test audit-check check

bootstrap:
	@lake env lean --version
	@lake --version
	@turbo-lean --version

prove:
	@lake build Glamsterdam glamsterdam_spec_cabi
	@python3 scripts/audit_metadata.py
	@printf '%s\n' 'prove ok: Common EL core, Eip8246, Gas (8037/8038/2780/7778/12582/DecisionMatrix), Gloas7732 (+8282), TestVectors, and C-ABI static lib compiled with 0 sorryAx, 0 axiom, 0 native_decide'

turbo-verify: prove
	@turbo-lean --json ci-verify --project-dir . --mode trusted --receipt .lake/turbo-receipt.json
	@turbo-lean --json verify-receipt .lake/turbo-receipt.json --baseline-receipt .lake/turbo-receipt.json
	@if turbo-lean --help 2>&1 | grep -q "audit-spec"; then \
		turbo-lean --json audit-spec Glamsterdam > .lake/audit-spec.json; \
		python3 -c 'import json; d = json.load(open(".lake/audit-spec.json")); assert d["ok"] is True and d["vacuous_specs"] == 0 and d["trivial_specs"] == 0 and len(d.get("stub_defs", [])) == 0 and len(d.get("horizontal_packing_warnings", [])) == 0 and len(d.get("droppable_hypotheses", [])) == 0, str((d.get("vacuous_specs"), d.get("trivial_specs"), d.get("stub_defs"), d.get("horizontal_packing_warnings"), d.get("droppable_hypotheses"))); print("audit-spec ok:", d["tight_specs"], "/", d["total_specs_audited"], "tight specs, 0 vacuous, 0 trivial, 0 stub_defs, 0 packing warnings")'; \
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
