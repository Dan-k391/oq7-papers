# S4 — Audit provenance

The preserved [final audit report](AUDIT_REPORT_686402a.md) examines commit `686402a6c2d63820828729cc7ab02504632e3fe7`, tree `580737ccf6557102d601894145cc0229ae1f83e3`, and declaration `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement`.

Report SHA-256: `59a36c60a01d213c989ddf7547fbc63584770101b6eb5a6818bb3ad0d5f91eed`. The report contains no explicit audit date. The source ZIP and Git bundle are identified in the [frozen manifest](manifest.json).

| Evidence | Supplied record | Scope |
|---|---|---|
| Kernel checking | Frozen manifest, source archive, final audit report | Encoded theorem in pinned Lean 4.34.1; final-theorem dependency axioms are `propext`, `Classical.choice`, and `Quot.sound` |
| Main-statement semantic/model review | Final audit report and [status summary](final-audit-status.json) | AI-assisted review reports PASS for the October 11 Theorem 1.1/Lemma 1.2 and closure of preceding findings F1–F4; the [preserved version comparison](MANUSCRIPT_VERSION_CORRESPONDENCE.md) maps these to Theorem 4.1/Lemma 4.2 |
| Same-kernel fresh replay | Frozen manifest, final report, [historical October 13 checking record](current-verification.json) | Empty-environment replay by Lean's own kernel implementation; the October 13 record reports exit 0 |
| Manuscript correspondence | [S1 table](../theorem-correspondence.html) and [scope note](CORRESPONDENCE_AUDIT_SCOPE.md) | Main-claim mapping distinguishes direct formal declarations, consequences, and differently organized expository arguments |

The October 13 checking record describes an earlier isolated checkout using compatible cached build objects, followed by a fresh same-kernel replay. Its build is not a new from-source dependency build, and it is not a checking record for this publication revision. Historical manifest fields and manuscript-version descriptions retain their original dates and scope; the completed final report supersedes the frozen manifest's export-time pending semantic-review field.

The final semantic verdict concerns the encoded main theorem within the stated two-layer Maxwell model. It does not certify every intermediate lemma or paragraph of the manuscript's reorganized proof presentation. The supplied mathematical and semantic reviews are AI-assisted. Completed human peer review, an independently implemented kernel checker, and first scientific priority are not established by this evidence.

The publication manuscript lists Daniel Wang (McMaster University) first and Junjie Zheng (Columbia University) second. Its edits and document validation are recorded separately in [CHANGES.md](../../CHANGES.md); the frozen mathematical source and historical reports retain their original identities. [Reproduction instructions](../../REPRODUCE.md) explain how to check the supplied proof archive.

