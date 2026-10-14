# Publication revision and review record

14 October 2026

The current manuscript is **Unit Supremum of Absorption Asymmetry at Prescribed Extinction for Compact Reciprocal Dielectrics**, by **Daniel Wang, McMaster University**, and **Junjie Zheng, Columbia University**, in that order. Student status is omitted. This revision prepares a professional manuscript and accompanying supplements while preserving the earlier review package and frozen proof archives.

The manuscript, both appendices, bibliography, rendered PDF, HTML, and publication documentation were reviewed. No demonstrated error in the central mathematical argument was found in this review. Lean source code was excluded from review and execution. The existing formal-verification claims retain their recorded audit scope.

## 14 October 2026 author correction

The initial named revision placed Junjie Zheng before Daniel Wang. The subsequent author-order instruction specifies **Daniel Wang first, Junjie Zheng second**, retaining McMaster University and Columbia University as their respective affiliations. This correction applies to the current repository manuscript, generated PDF/HTML author display and metadata, repository and publication landing pages, author-information table, supplement index, provenance, and this change record.

This revision updates files originating in this repository. The requested Git workflow is a direct commit and push to `main`. The external `GPTRESEARCH` and `GPTPROOF` folders were inspected read-only and left unmodified. No additional paper was created, and no author attribution was added to the preserved audit reports. The sealed review package and frozen mathematical sources remain unchanged.

## Changes to the manuscript

1. Added both authors and their supplied university affiliations to the title page. Added matching PDF author/title metadata and HTML author metadata.
2. Changed the title from “Unit Absorption Asymmetry” to “Unit Supremum of Absorption Asymmetry” to make strict nonattainment clear.
3. Rewrote and shortened the abstract. Replaced “reciprocity fixes the extinction” with the precise statement that reciprocity equates the two extinction cross sections. Retained the exact target, material caps, compact two-layer class, uniform normalized aperture step, positive-loss regularization, resource assumptions, and verification scope.
4. Shortened Section 2 by consolidating related literature comparisons and removing repeated priority commentary and a link to an internal working report. Retained all 20 cited references and the statement that first priority is unresolved. Citation numbering was regenerated in order of first appearance.
5. Corrected the flux wording in the proof of Lemma 5.1: the sphere-integrated time-averaged Poynting flux **divided by incident intensity** tends to the scattering cross section. Explicitly identified the unit-amplitude incident intensity as \(I_{\rm inc}=1/(2Z_0)\).
6. Defined the absorber vacuum phase \(v_A=e^{ikh}\) in Section 6.1 before its first use in the cascade formula.
7. Specified in Section 8.1 that the selected extinction roots lie in the constructed angle bracket, so the following asymptotic claim applies unambiguously to those roots.
8. Replaced the incidence labels \(h,\ell\) in Section 9 with \(\mathrm{hi},\mathrm{lo}\), avoiding reuse of the absorber-thickness symbol. Updated equations (44)–(45) and their explanatory text; the mathematical relations are unchanged.
9. Shortened Section 10 to the main formal statement, correspondence scope, archived audit categories, and S1–S4 availability. Removed repeated audit chronology, intermediate audit-theorem names, export logistics, anonymous-copy wording, and the statement that a public archival location is unspecified. Materials are described as accompanying supplements; no public archive or DOI is invented.
10. Retained a concise AI-assistance disclosure with its documented task scope. Retained the distinction between the formal main theorem and the manuscript's differently organized proof presentation, and between AI-assisted review, human peer review, and same-kernel checking.
11. Removed a redundant simulation/experiment disclaimer in Section 9; the absence of experimental and simulation datasets is stated once in the availability paragraph. Tightened the final sentence of the conclusion.
12. Removed the internal priority-review note from the Mann–Alù bibliography entry. Its authors, title, year, conference description, and official source URL are retained; the source-access limitation remains in Section 2.
13. Set the bibliography in 10-point type, eliminating the otherwise nearly empty page containing only the final reference. The final PDF has 15 pages; the main text remains 11-point.

## Changes to document generation and packaging

1. Created `publication/` as the single current named revision. The previous manuscript, frozen copies, reports, manifests, and Lean files remain unchanged in their original locations.
2. Updated the HTML template to render both authors and affiliations visibly and to emit separate author metadata. Adding LaTeX authors alone would not have populated the previous HTML header.
3. Corrected inline MathML styling to avoid tiny native scroll controls while retaining inline equations. Kept the existing offline MathML conversion and displayed-equation layout.
4. Extended the manuscript builder with `--xelatex` and `--bibtex` options, using three XeLaTeX passes and a BibTeX pass. Retained the Tectonic route and `--skip-pdf` option. Added extraction of author names from the LaTeX-derived document metadata for HTML metadata.
5. Rewrote the repository landing page around the current title, named authors, manuscript, claim scope, and scientific evidence. Marked earlier partial or pending milestone documents as historical in that navigation.
6. Added concise publication landing, author-information, and reproduction documents. Reproduction instructions use portable executable arguments, distinguish the manuscript build from frozen proof reproduction, and state that the compiler and dependencies are obtained separately.
7. Replaced the supplement index and provenance in this new revision with concise scientific descriptions. Removed recipient email, connected-account, permission, and transmission workflow commentary from these current documents. Historical records retain their original identities and are labeled by their actual scope and dates.
8. Copied the correspondence table, figure assets and generator, frozen source ZIP and Git bundle, and supporting audit/verification records into the new revision. The source ZIP and bundle are byte-identical to the frozen manifest.
9. Added `.publication-work/` and `publication/manuscript/build/` to `.gitignore` so downloaded conversion tools, page renders, and temporary build files are excluded from ordinary Git additions. Downloaded the official Pandoc 3.12.1 Windows archive into the isolated working directory and checked its SHA-256 against the official release digest.
10. Saved this change record, a source diff, a complete file/hash inventory, document-check results, and a new checksum manifest. Created a distribution ZIP containing the current publication files and supplements, excluding tool executables, build caches, render images, old email drafts, and the full historical repository.

## Files changed or added

The two modified pre-existing repository files are `README.md` and `.gitignore`. All remaining publication files are new; no file under the original `review-package/` was edited.

| File or group | Action |
|---|---|
| `README.md` | Rewritten current repository landing page |
| `.gitignore` | Added two working/build exclusions |
| `publication/README.md` | Added current document index |
| `publication/AUTHOR_INFORMATION.md` | Added supplied author names and affiliations |
| `publication/REPRODUCE.md` | Added portable manuscript and frozen-proof instructions |
| `publication/manuscript/main.tex` | Copied the current review source and applied the manuscript edits listed above |
| `publication/manuscript/references.bib` | Copied bibliography and removed one internal review note |
| `publication/manuscript/build.py` | Copied builder and added XeLaTeX/BibTeX and author-metadata handling |
| `publication/manuscript/template.html` | Copied template and corrected author rendering and inline MathML styling |
| `publication/manuscript/paper.pdf`, `paper.html`, `main.bbl` | Regenerated publication outputs and bibliography |
| `publication/manuscript/figures/two-layer-geometry.pdf`, `.svg` | Copied unchanged vector assets |
| `publication/manuscript/review/make_geometry.py` | Copied unchanged figure generator |
| `publication/manuscript/theorem-correspondence.html`, `.csv` | Copied unchanged S1 correspondence |
| `publication/manuscript/reproducibility/AUDIT_PROVENANCE.md`, `SUPPLEMENT_INDEX.html` | Added current concise provenance and named supplement navigation |
| Other files in `publication/manuscript/reproducibility/` | Copied unchanged historical evidence and frozen proof archives; individual paths and hashes are in the inventory |
| `publication/CHANGES.md` | Added this complete revision and review record |
| `publication/SOURCE_CHANGES.diff` | Added exact manuscript, bibliography, builder, template, and repository text diffs |
| `publication/CHANGE_INVENTORY.json` | Added individual file identities and baseline-copy classifications |
| `publication/verification/DOCUMENT_CHECK.json` | Added current document and link verification results |
| `publication/verification/MANUSCRIPT_BUILD.json` | Added publication build versions and commands without machine-specific private paths |
| `publication/SHA256SUMS` | Added checksum manifest for the new revision |
| `publication-bundle-2026-10-14.zip` | Added the distribution archive outside the publication directory |

Generated intermediate `.aux`, `.log`, `.out`, build JSON, PDF copies, page PNGs, downloaded Pandoc files and their identity record reside in the ignored working/build directories. They are excluded from the distribution archive. No email was sent, external repository changed, paper uploaded, or publication submitted.

## Verification and review findings

- XeLaTeX and BibTeX compiled the manuscript successfully; Pandoc 3.12.1 generated the HTML. There are no final LaTeX citation/reference warnings, overfull boxes, or underfull boxes.
- All 51 numbered equations and all theorem, lemma, and proposition statements were retained. Forty-nine equations are text-identical after whitespace normalization; the other two differ only by the stated incidence-label renaming.
- All 20 bibliography entries are cited. TeX labels and references resolve, HTML IDs are unique, and manuscript/supplement links resolve within the distribution directory.
- PDF title and author metadata match the visible title page. The PDF page layout, figure, formal-status paragraph, and complete bibliography were visually inspected. HTML author display, inline MathML, displayed equations, image loading, and desktop layout were checked in the browser.
- The copied proof archives match their original frozen hashes. The existing sealed package was preserved. Its compiler archive remains a documented separate asset rather than an advertised file in this smaller publication distribution.
- Primary bibliographic records support the OQ7 tutorial and the recent Máñez-Espina reference. The official Mann–Alù program confirms the qualitative precedent; comparison with its unrecovered full equations and with the complete Gao paper remains unresolved. The manuscript retains appropriately limited novelty wording.

The machine-readable results are in [DOCUMENT_CHECK.json](verification/DOCUMENT_CHECK.json). Individual files and baseline identities are in [CHANGE_INVENTORY.json](CHANGE_INVENTORY.json), with text edits in [SOURCE_CHANGES.diff](SOURCE_CHANGES.diff).

## Final author and submission decisions

The document and packaging issues identified in this review have been addressed. The manuscript is prepared for final author review and submission as a general scholarly manuscript; no specific venue's submission requirements have been supplied.

1. The author order follows the supplied instruction: Daniel Wang first, Junjie Zheng second. Both authors should review the affiliations and AI-assistance disclosure. The available records document manuscript preparation and AI-assisted review. If AI also assisted the original mathematical derivation or proof-code creation, add that actual scope before publication. No unsupported human contribution or verification claim was inserted.
2. Supply the corresponding-author email, contribution statement, ORCID IDs, and venue formatting only where the chosen journal or preprint service requires them.
3. Publish the paper together with S1–S4. The local supplement links work in this distribution; publishing the PDF by itself requires replacing them with the actual hosted supplement URLs or archival identifier once assigned.
4. Choose the requested publication and source-reuse license through the selected venue/archive. No license, DOI, public-release status, or first-priority assertion was invented.
