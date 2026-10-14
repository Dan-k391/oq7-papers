# Separate release revision

Frozen audited commit: `686402a6c2d63820828729cc7ab02504632e3fe7`.
Portable release commit: `0bdf00f9b75b43194436f9536b1bf09463fd5a5d`.
The original commit, source ZIP, Git bundle, theorem and historical manuscripts remain unchanged. The release commits are confined to a disposable repository.

## Final changes

- R1: lake-manifest.json is included and tracked; its git-ignore rule was removed. sources/pinned-lake-manifest.json remains the tracked recovery copy.
- R2: lakefile.toml now uses the relative .lake/packages directory. Existing configure.py/configure.ps1 restore that default without changing a revision.
- Environment placeholders: portable top-level env.sh/env.ps1 use lake env; no manually assembled LEAN_PATH or machine-specific package path is required. The exact original auditor env.sh remains historical evidence.
- Added byte-preserved final audit programs/logs/report, preceding report, run-audit.py and a safe offline restore helper.
- Exported all nine dependency source ZIPs and Git metadata snapshots. Empty metadata directories are retained. Symbolic-link blobs are materialized as ordinary link-text files, matching core.symlinks=false, so restoration creates/follows no links.
- New manuscript edits change completed-audit status and review distinctions only. MANUSCRIPT_CHANGES.diff records them. Scientific theorem and equation environments remain unchanged.

All 378 mathematical library files have the same SHA-256 as the frozen originals. Added auditor theorems live under audit/final/experiments/; they do not replace or modify theorem11_complete. No dependency upgrade was made.

## Exact repository differences

```text
M	.gitignore
A	RELEASE_REPRODUCE.md
A	audit/final/AUDIT_REPORT_686402a.md
A	audit/final/env.sh
A	audit/final/experiments/Audit2.lean
A	audit/final/experiments/AuditCone2.lean
A	audit/final/experiments/AuditExperiments.lean
A	audit/final/experiments/AuditWholeProject.lean
A	audit/final/logs/build-all.log.gz
A	audit/final/logs/cone2.log
A	audit/final/logs/experiments2.log
A	audit/final/logs/leanchecker-fresh-PhysicalTheorem11.log
A	audit/final/logs/regression-experiments.log
A	audit/final/logs/whole-project-axioms.log
A	audit/preceding/AUDIT_REPORT_5a8350d.md
A	env.ps1
A	env.sh
A	lake-manifest.json
M	lakefile.toml
A	restore-dependencies.py
A	run-audit.py
```

PACKAGING_CHANGES.diff supplies the full patch. Manuscript changes are outside this Git revision and have separate checksums and a full diff.

## Tests and scope

Current commands/logs are in portable-test-logs/ and results in PORTABLE_TEST_STATUS.json. The included compiler/dependency version checks and offline dependency round-trip are separate from the completed final semantic audit. This run tests on Windows; POSIX execution was not performed here.

The first offline restoration test rejected three dependency link entries; the helper was corrected to preserve their Git blob bytes as link-text without creating links. The next test found omitted empty Git metadata directories; export was corrected. Both failed attempts and the successful retest are retained. These were packaging tests, not failures of the audited theorem.
