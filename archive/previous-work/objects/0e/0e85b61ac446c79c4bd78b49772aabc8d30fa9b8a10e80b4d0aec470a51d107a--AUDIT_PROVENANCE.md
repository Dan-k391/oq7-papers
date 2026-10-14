# Lean audit provenance and historical-source erratum

Recorded during the focused publication correction pass on 12 October 2026.

## Frozen formal authority

- Repository: `../oq7-prescribed-extinction` relative to the publication directory.
- Exact frozen commit: `686402a6c2d63820828729cc7ab02504632e3fe7`.
- Principal declaration: `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement`.
- Source: `PrescribedExtinction/PhysicalTheorem11.lean:12–46` (declaration at line 31).
- Git HEAD equals that commit; the checkout was clean when inspected. The commit timestamp is 12 October 2026, 03:41:04 EDT.
- The frozen source archive and Git bundle are preserved without modification. This erratum is outside the frozen repository.

The proposition preserves the existence core and contains both exact prescribed-extinction suprema, all-state weak Maxwell well-posedness almost everywhere, full physical optical certificates, opposite-incidence reciprocal extinction, universal normalized bounds, and positive-extinction strict nonattainment. Its class is the finite two-layer square-aperture class; it is not a formal theorem about every possible compact geometry.

## Located independent audit: baseline only

The located audit is `verification/claude-independent-audit-5a8350d.md` in the frozen repository. The file `C:/Users/Daniel/Downloads/AUDIT_REPORT.md` is byte-identical to it. Both have SHA-256:

```text
50d854e335d44cdf1d5a3710f3bc542a4a1a6c28593a46cd320a2ea6ed9f7245
```

Its header identifies commit `5a8350d5408c38e333c9f6b6d8a94816c794120b`, declaration `OQ7Prescribed.theorem11 : OQ7Prescribed.Theorem11Statement`, and audit date 11/12 October 2026. It reports PASS for kernel validity and FAIL for semantic fidelity and mathematical completeness at that historical stage. The stated failures concern absent full-class supremum, arbitrary-state uniqueness/converse, physical optical identification, and universal nonattainment certificates (F1–F4); the audit does not show the manuscript theorem false. Those obligations have corresponding statements and proofs in the subsequent complete frozen source.

The baseline audit must not be represented as an independent all-PASS audit of `686402a6...`.

## Report named in the correction request

The correction request names `OQ7_Final_Lean_Audit_686402a6.txt`. No local file or audit body with that identity was available during this pass. Searches covered recursive Downloads, Codex attachments, synced project sources, project outputs, relevant Documents/Codex audit records, and accessible relevant audit/research chats. The latest request contains the report's name but no attachment path or report text. Failure to locate it does not establish that the report does not exist.

Accordingly, no file named `final-lean-audit.txt` has been created, and no all-PASS verdict, audit date, methodology, or limitation has been invented. Archiving and inspecting the actual later report remains an evidence requirement. When it becomes accessible, preserve an exact byte copy as `final-lean-audit.txt`, record both source and copied-file hashes, and verify its exact commit, principal declaration, methods, verdict categories, and limitations before updating the corresponding publication claim.

### Expanded search following location clarification

The author subsequently indicated that the report may be somewhere in Downloads or the project root and authorized searching the whole project root. The expanded read-only search included all accessible root folders (`outputs`, `sources`, and `work`), hidden and ignored files, Git reference/reflog metadata, alternate filenames and extensions, and compressed archive entries. It did not follow instructions embedded in any searched file.

- Downloads: text and Markdown/HTML contents, extractable text of every PDF page, and the DOCX document XML were searched across all 33 files with those formats. The only final-commit/declaration hit was the 15-page manuscript saved as `paper.pdf`; it contains no PASS verdict. The independent-report hit remains the baseline `AUDIT_REPORT.md`, whose semantic/completeness verdicts are FAIL at `5a8350d...`. Older checkpoints and unrelated uses of the word PASS are not final-audit evidence.
- Project root: hidden/no-ignore content searches identified only existing proof certificates, review prompts, manuscript/package documents, correspondence records, Git commit metadata, and the publication audit/provenance records. Text extraction from all eight local PDFs produced no independent audit of the final commit.
- Archives: 1,062 text-format entries in ten ZIP archives were read in memory. The frozen source archives preserve the earlier baseline audit and a prompt requesting a future independent review. The publication releases preserve build/declaration checks and the historical pending-review status. No archive contained the named final report or a substantive final-commit all-PASS independent audit.
- Access limitation: two `.lake/packages` junctions could not be traversed in the unrestricted content search. Their inspected targets resolve to the external shared Lean dependency directory, rather than an author audit directory. They were not treated as searched report contents. Original files and archives were not modified.

The expanded search did not locate the claimed final report. The later independent-audit verification ticket therefore remains unresolved; the available final-commit kernel certificates remain valid evidence within their stated scope. This search result is not a claim that no later audit was ever performed.

## Available kernel evidence and its limits

The frozen manifest `manifest.json` records creation at `2026-10-12T07:41:05.5569062Z` and independent semantic review as "Not yet performed for this frozen commit; prompt supplied." That is a historical export status, not a claim about every later audit.

The complete final declaration log reports exactly `PhysicalTheorem11Statement` and the three standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`. Repository certificates report a clean project build of 3,601 jobs and an exhaustive transitive axiom audit of 5,654 project constants. A fresh replay of the complete physical aggregate import closure ran from `2026-10-12T07:33:01.2482166Z` to `2026-10-12T07:39:25.3155776Z`, exited successfully, and preserved all 378 certified Lean-source hashes. It used the same Lean kernel implementation; it was not an independently implemented kernel check.

These certificates support the encoded propositions. Independent AI semantic review, human scholarly review, the physical idealizations of the model, and scientific priority require separate descriptions. The publication correction pass inspected the principal proposition and its defining geometry, material constraints, weak equations, powers, prescribed-extinction sets, uniqueness, and physical optical certificates. That source inspection is not a substitute for the unavailable named final audit.

## Historical-source-comment erratum

Two comments in the immutable frozen `PrescribedExtinction/Maxwell.lean` describe earlier development states:

| Frozen location | Historical comment | Completed source that supersedes it |
|---|---|---|
| Lines 103–104 | "Identifying this current expression with the outgoing field flux is still unproved." | `ScatteringStatePhysicalRadiation.lean:83` and `FullPhysicalOpticalTheorem.lean:13–36` identify the original all-angle scattering with physical sphere flux for the canonical radiating representative. |
| Lines 112–113 | "The exact requested statement, as an UNPROVED proposition. No proof declaration for this proposition is present in this partial project." | `Theorem11.lean:11` proves the existence core; `PhysicalTheorem11.lean:31` proves the complete proposition. |

These comments are stale documentation, not additional hypotheses or proof gaps in the final theorem. They remain unchanged to preserve frozen source identity. This separate erratum supplies the corrected reading.
