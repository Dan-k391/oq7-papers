# OQ7 prescribed-extinction release

The completed final audit of commit 686402a6c2d63820828729cc7ab02504632e3fe7 reports PASS for kernel checking, main-theorem semantic fidelity and F1-F4 closure. This release incorporates that existing evidence, preserves all originals and supplies a separate portable packaging revision. It is a local release package; nothing was published, submitted or sent.

| Location | Purpose |
|---|---|
| frozen/ | Exact audited source ZIP, complete original Git bundle and historical verification manifest |
| evidence/AUDIT_REPORT_686402a.md and evidence/oq7-final-audit-686402a.zip | Byte-preserved final report and audit packet |
| evidence/final/ | Extracted audit programs and logs, plus readable decompressed build log |
| evidence/preceding/ | Recovered preceding audit of 5a8350d |
| evidence/manuscripts/ and evidence/publication-baseline/ | Preserved October 11 scientific specification and newer publication baseline |
| dependency-sources/ | All nine exact pinned dependency source snapshots, Git metadata snapshots and pin manifest |
| portable-source.zip and portable-release.bundle | Separate portable release revision; mathematical sources unchanged |
| manuscript/ | Updated LaTeX source, bibliography, assets, 16-page PDF, offline HTML and updated S1-S4 supplements |
| MANUSCRIPT_VERSION_CORRESPONDENCE.md | Precise Theorem 1.1/Lemma 1.2 to Theorem 4.1/Lemma 4.2 comparison and scope limits |
| AUDIT_PROVENANCE.md | Final/preceding review identities and distinctions among kernel, replay, semantic and human review |
| REPRODUCE.md | Portable locked-dependency build and audit-program instructions |
| RELEASE_DIFFERENCES.md and PORTABLE_TEST_STATUS.json | Exact packaging changes, mathematical-source preservation and current tests |
| portable-test-logs/ | Complete commands, exit codes, versions, warnings and output from this run |
| PRIORITY_QUESTIONS.md | Short list of unresolved equation-level priority comparisons |
| SHA256SUMS | Content checksums for every release file except the checksum manifest itself |

The complete source-and-audit archive is supplied beside this directory. SHA256SUMS uses relative paths from the release root. The separate archive checksum is supplied beside the archive to avoid a self-referential checksum.

## Completed proof/audit work

The frozen main theorem and its semantic/model audit are completed evidence. Both suprema and nonattainment, arbitrary-state well-posedness/optics/reciprocity and F1-F4 are covered within the formal two-layer model. auditor_extinction_pos and related auditor lemmas are preserved as separate evidence. The final report records successful fresh replay using the same Lean kernel; no independently implemented checker is claimed.

## Release work and remaining tasks

The current release adds portable configuration, a tracked root manifest, dependency snapshots, completed-audit supplements, manuscript-status revisions, exact differences and recorded tests. The audit does not establish human peer review, scientific priority, finite bandwidth, fixed-resource performance or every interpretation of OQ7. Those are external or separately scoped questions, not pending repetitions of the completed final audit.

Portable release commit: `0bdf00f9b75b43194436f9536b1bf09463fd5a5d`. Original audited commit: `686402a6c2d63820828729cc7ab02504632e3fe7`. All 378 mathematical library source hashes are unchanged.

## Current-run validation completed

The portable Windows build passed 3,601 jobs and compiled the final PhysicalTheorem11 module. The exact final declaration/axiom check and all four preserved audit programs passed. All nine offline-restored dependency snapshots matched their pinned revisions and clean-source checks. All 378 mathematical source hashes, 6,196 original project-file hashes and both attached audit files are unchanged. The updated PDF remains 16 pages, with 51 equations and 20 references; all rendered pages were inspected.

Complete warnings are preserved in the build log; they are linter/deprecation diagnostics, with no admitted-proof warning. No additional fresh kernel replay or independent checker is claimed for this release run; the supplied final audit's completed replay remains accompanying evidence. POSIX execution and human peer review were not performed here.
