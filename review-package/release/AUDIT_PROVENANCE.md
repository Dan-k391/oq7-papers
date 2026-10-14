# Completed audit provenance

## Exact final evidence

- Audited commit: `686402a6c2d63820828729cc7ab02504632e3fe7`.
- Audited tree: `580737ccf6557102d601894145cc0229ae1f83e3`.
- Declaration: `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement`.
- Attached report: evidence/AUDIT_REPORT_686402a.md, SHA-256 `59a36c60a01d213c989ddf7547fbc63584770101b6eb5a6818bb3ad0d5f91eed`.
- Attached packet: evidence/oq7-final-audit-686402a.zip, SHA-256 `1e0c28039e81bcd9b5531a1e0d0e122190ef9780e9fec8d164467b5b1b032d30`.
- The report inside the packet is byte-identical to the standalone attachment.
- The report itself supplies no explicit audit date; this release does not invent one.

The final report records PASS for kernel validity, semantic fidelity to the October 11 Theorem 1.1/Lemma 1.2, Maxwell correctness within the formal model, both suprema/nonattainment, closure of F1-F4, and reproducibility with packaging defects R1/R2. These are completed existing audit results, not open proof obligations.

The accompanying audit programs, compressed build log and other logs are retained byte-for-byte under evidence/final/ and in the portable repository's audit/final/. A decompressed copy of build-all.log is provided in evidence/final/logs/ for convenience; the original .gz is preserved.

## Preceding audit recovered

evidence/preceding/AUDIT_REPORT_5a8350d.md has SHA-256 `50d854e335d44cdf1d5a3710f3bc542a4a1a6c28593a46cd320a2ea6ed9f7245`. It is the preserved `verification/claude-independent-audit-5a8350d.md` from the frozen repository, examining commit `5a8350d5408c38e333c9f6b6d8a94816c794120b`, tree `a1b03d72e958851f2418f97a6b5c40c0689e305c`. Its kernel PASS and semantic/completeness FAIL described the existence-only stage; the final report closes those F1-F4 findings at the final commit. The regression program AuditExperiments.lean is also present in the final packet.

## Supplemental auditor theorems preserved

audit/final/experiments/Audit2.lean retains `auditor_extinction_pos`, `auditor_universal_gamma_lt_one`, `auditor_sup_is_lub` and the associated checks. The positive-extinction result rules out the formal division-by-zero branch for every admissible body/state. It remains accompanying audit evidence; it has not been silently inserted into or substituted for the frozen main theorem.

## Distinct kinds of evidence

| Evidence | What it establishes | Boundary |
|---|---|---|
| Lean kernel checking and standard-axiom census | Encoded theorem/proofs checked with Lean 4.34.1; only propext, Classical.choice, Quot.sound | Relative to that kernel/toolchain and definitions |
| Fresh replay independently run by the final auditor | PhysicalTheorem11 import closure replayed into an empty environment; reported exit 0, 10 min 45 s | Uses Lean's same kernel implementation; no independently implemented checker was used |
| AI-assisted semantic/model review | Reviewer's PASS correspondence and F1-F4 closure in the stated model | Distinct from human peer review and novelty |
| Current portable-release tests | Recorded commands/logs test the packaging revision and preserved audit programs | Not a newly commissioned generic audit |
| Human peer review | No completed human peer-review evidence supplied | Remains an external-review task |
| Scientific priority | Not established by any kernel or semantic verdict | Equation-level prior-art comparisons remain separate |

The final report's cone count is 61,839 constants; its whole-project sweep reports 5,658 project constants (49 private). The repository's historical count is 5,654. The report attributes this small difference to generated-declaration counting; both report the same three foundation axioms. Counts are not equated or used as a novelty measure.

## Historical metadata preserved

The immutable frozen manifest's export-time field says semantic review was not yet performed. It is retained as historical provenance and is superseded for current status by the attached completed final report. Likewise, earlier publication issue/provenance records remain unchanged in evidence/publication-baseline/. The release supplements now point to the final report and companion status record, rather than presenting those historical pending fields as current.

The corrected root was explicitly reauthorized by the user. The mistaken literal root was tested and returned PathNotFound. The two Downloads attachments were read by their explicitly supplied exact paths; Downloads was not searched. Originals and synced files were preserved. The earlier source inventory skipped both dependency junctions and recorded them; no external source link was followed.

The current portable Windows test reused compatible cached dependency objects and compiled the project modules fresh. It does not claim a fresh from-source Mathlib build or a new kernel replay. All four preserved auditor programs were rerun successfully; exact output and warnings are in portable-test-logs/.
