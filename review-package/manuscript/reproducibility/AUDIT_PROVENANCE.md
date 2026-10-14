# S4 — Final review-package audit provenance

The authoritative completed final audit is the byte-preserved release/evidence/AUDIT_REPORT_686402a.md, SHA-256 59a36c60a01d213c989ddf7547fbc63584770101b6eb5a6818bb3ad0d5f91eed. Its packet is release/evidence/oq7-final-audit-686402a.zip, SHA-256 1e0c28039e81bcd9b5531a1e0d0e122190ef9780e9fec8d164467b5b1b032d30.

It examines commit 686402a6c2d63820828729cc7ab02504632e3fe7, tree 580737ccf6557102d601894145cc0229ae1f83e3 and OQ7Prescribed.theorem11_complete. The report contains no explicit audit date; this package does not invent one.

| Evidence category | Actual supplied evidence | Scope and limitation |
|---|---|---|
| Lean kernel checking | Frozen certificates, completed final audit and regenerated strict type/axiom checks | Encoded main theorem in pinned Lean 4.34.1; dependency axioms limited to propext, Classical.choice, Quot.sound |
| Mathematical/model review | Completed final report and preserved MATHEMATICAL_CONSISTENCY_ORIGINAL.md | AI-assisted assessment; ordinary source review of specified revisions, not human certification of every manuscript line |
| Semantic fidelity | Final report PASS for October 11 Theorem 1.1/Lemma 1.2 and F1–F4 closure | Main-statement correspondence; newer Theorem 4.1/Lemma 4.2 map preserved separately |
| Same-kernel fresh replay | Original frozen and final-auditor replay records, plus the completed current verification/KERNEL_REPLAY.log and exact command record (exit 0) | Empty-environment replay by Lean's own kernel implementation; not an independently implemented checker |
| Independently implemented kernel checker | No completed evidence supplied or produced | Not performed; no such claim made |
| Human mathematical/semantic peer review | No completed review evidence supplied | Not established; anonymous copy is for review |
| Priority comparison | Existing priority/TARGETED_PRIORITY_REPORT.md and source registry | Completed bounded AI-assisted investigation; first priority remains unresolved because of specified access and equivalence gaps |
| This finalization run | verification/ logs, document preservation, rendering, bibliography and package checks | Targeted release verification; no new research, generic audit, or new proof commissioned |

The preceding report at release/evidence/preceding/AUDIT_REPORT_5a8350d.md examined 5a8350d5408c38e333c9f6b6d8a94816c794120b. Its kernel PASS and semantic/completeness FAIL applied to the existence-only stage. Final F1–F4 closure is not described as pending merely because that older report or the frozen export manifest predates it.

The standalone ordinary manuscript consistency review examined source db316052e8d93d379696b6d4fa392b51adad35fa23ae05739fb60a5380729884 and PDF aa3a3fdb569a69d9fef82ecd54fe94d346f3723a0e65f597c24ac18ee3e1890d. Its older statement that no final all-PASS audit was archived describes its own evidence at that time. The final report is now recovered and preserved alongside it, without rewriting the historical review.

auditor_extinction_pos, auditor_universal_gamma_lt_one, auditor_sup_is_lub and the related checks are retained in Audit2.lean and the current regenerated audit-program logs. No supplemental auditor lemma replaces or modifies the frozen main declaration.

The final report's 61,839-cone and 5,658 whole-project constant counts differ from the repository's historical 5,654 enumeration. These are retained with their originating reports; generated-declaration counting differences are not equated and counts are not used to establish novelty.

The current checkout uses the separate portable release revision, with exact frozen mathematical sources and pinned dependencies. Its ordinary Lake invocation reuses compatible build objects. The earlier clean project-build log is preserved; the current incremental log is not mislabeled a fresh from-source dependency build. The new same-kernel replay passed with exit 0 in 361.929 seconds and is recorded explicitly in CURRENT_VERIFICATION.json; it is not inferred from an earlier pass.

The review manuscript's AI-assistance disclosure describes this release work. Human author name, affiliation and corresponding-email facts are not inferred from local directory names or the connected Gmail account. No journal submission, preprint publication or author/library contact is authorized by this package. The user separately authorized sending the paper to denialk391@gmail.com after final checks.

