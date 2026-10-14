# Changes for arXiv preparation on 14 October 2026

This record covers the current revision of the repository, starting from main commit `b42fc156a4106fd5a6b6d0f516ad5a8b291103fe`. All five manuscript groups are revised, following the user's clarification that the task covers every paper. Quartic-Maxwell and generalized-research were prioritized for substantial reconstruction; fixed-resource and compact-Maxwell sources are also reconstructed. The prescribed-extinction paper receives consistent metadata and source packaging.

Original TeX for the four dated companion papers is unavailable. Their new sources are reconstructed from the PDFs with the user's authorization. The historical PDFs, extracted text, audit reports, imported baseline publication and frozen evidence are preserved. No Lean code was reviewed, edited or executed.

## Authors and contact details

- Set the order to Daniel Wang, then Junjie Zheng, throughout all five current source revisions and PDF metadata.
- Used McMaster University and Columbia University as their respective current affiliations; omitted student status and did not invent departments, ORCIDs or contribution roles.
- Included `denialk391@gmail.com` and `zjj2785@gmail.com` for lasting correspondence. The supplied school emails are recommended for the authors' arXiv accounts while accessible; they are not the sole contact details in the manuscripts.
- Used a fixed manuscript date, 14 October 2026, avoiding changing dates on later compilation.
- Standardized the author blocks: name, university and a blue clickable email in the same monospaced font, in identical author order across all five manuscripts. No mixture of plain-text contacts and email links remains.

## Quartic Maxwell manuscript

The new title is **Uniform Quartic Bounds for Reciprocal Absorption–Scattering Asymmetry**. The full scientific disposition and original section mapping are in [REVISION_NOTES.md](papers/quartic-maxwell/arxiv/REVISION_NOTES.md).

1. Reconstructed editable TeX and a separate BibTeX bibliography from the 17-page original PDF, rather than altering PDF page images.
2. Rewrote the abstract and opening around the uniform geometric theorem, static coefficient formula and finite-sphere certificates. Distinguished sharpness of the exponent from an optimal coefficient or exact finite-size optimum.
3. Explicitly required a measurable essentially bounded susceptibility, `chi in L-infinity(D; C^(3x3))`. Pointwise matrix bounds alone do not supply this hypothesis; the original adversarial audit identified the omission.
4. Retained the exact quartic inequality and its constants, the fixed-pattern coefficient formula and sixth-order remainder, the heterogeneous-sphere rational interval and quantitative remainder, and the homogeneous construction for every resource pair. Retained their complete analytic arguments.
5. Distinguished the fixed-pattern sixth-order remainder from a remainder uniform over every admissible design. Did not import stronger class-uniform claims from the separate October 11 continuation.
6. Clarified incident intensity, cross-section units, the full outgoing sphere, the time-reversed linear-polarization pair, operator versus scalar notation, and the canonical exterior representative of weak fields.
7. Added the full entire-vacuum uniqueness argument needed for the converse volume representation on arbitrary measurable supports.
8. Explained the enclosing-radius convention and conversion to the two-sphere minimum enclosing radius.
9. Added equation-level comparisons with primary small-inclusion and coupled-dipole precedents. Presented fixed-shape quartic scaling as an inference from earlier expansions and the sphere mechanism as established. Did not certify scientific priority.
10. Removed the original workflow/recovery narration, audit checklist, unverified source-archive promises, and numerical solver/convergence section from the revised paper. The original numerical record remains preserved. The analytic proofs establish the stated certificates without claiming a new numerical replay.
11. Replaced the long historical bibliography with the primary references actually used by the revised argument and comparisons; retained unresolved priority leads in the revision notes.
12. Added a concise, truthful AI-assistance and verification-scope statement. The prescribed-extinction formal audit is not applied to these results.

## Generalized research manuscript

The new title is **Reciprocal Absorption Asymmetry: Sharp Channel Tradeoffs and Dielectric Thickness Asymptotics**. The detailed theorem/section mapping is in [REVISION_NOTES.md](papers/generalized-research/arxiv/REVISION_NOTES.md).

1. Reconstructed editable TeX and bibliography from the 41-page PDF and reorganized the paper around the restricted scalar thickness theorem and sharp prescribed-overlap channel envelope.
2. Replaced the research-report opening, status badges and mandatory novelty-check table with a research introduction and direct attribution of established two-port/passivity results.
3. Retained the full ordinary proofs needed for the scalar material floor, exact-target thickness law, matching finite-layer construction, real implicit-function target matching and passage to every sufficiently large thickness budget.
4. Kept the thickness theorem's exact fixed targets and resources: positive transmitted power, strictly active mean absorptance, integrated scalar loss, positive material caps, arbitrary finite layer count and no imposed minimum feature size. Did not extend it to degenerate boundary targets or bounded layer count.
5. Retained the canonical channel reduction, positive-matrix certificate, middle-branch equality classification, outer constructions and continuous transitions. Distinguished an abstract reciprocal contraction from a local Maxwell realization.
6. Retained the planar vector construction and its physical role in exposing loss-free tensor subspaces. Corrected the claim of “finite geometry” to finite layer thicknesses and coefficients: the transverse material extent remains infinite, including for finite-power beam inputs.
7. Removed obsolete archive-recovery discussion, missing-theorem counts, agent-audit chronology, intermediate implementation paths, numerical-only appendices and overbroad formal-verification badges from the revised research narrative. Their historical records remain unchanged.
8. Corrected bibliography metadata against primary sources, including the Optica paper's page range **1746–1757**. Added complete author metadata where recovered and checked.
9. Corrected a reconstruction typo in the complex transmission-phase expression, and reviewed equation wrapping and references.
10. Kept a precise ordinary-proof/formal-scope distinction and AI-assistance disclosure. The scalar physical thickness theorem and complete channel envelope are not advertised as Lean-verified.

## Prescribed-extinction manuscript

1. Copied the existing named publication source, bibliography and required geometry figure into a new `arxiv/` revision; the imported publication remains unchanged.
2. Added lasting author contacts and a fixed date. The theorem, lemma, proposition, proof and equation bodies remain identical to the earlier named source.
3. Replaced local supplement hyperlinks with named ancillary files, avoiding broken PDF links or an unsupported claim that the private repository is publicly accessible.
4. Included byte-preserved frozen proof source, statement correspondence and version-specific verification evidence under `anc/`. Omitted the duplicate Git bundle and HTML navigation.
5. Adjusted the displayed long source-archive filename to prevent a margin overflow. This is a layout edit only.

## Fixed-resource bounds manuscript

The new title is **Resource-Dependent Bounds on Reciprocal Absorption–Scattering Asymmetry**. [REVISION_NOTES.md](papers/fixed-resource-bounds/arxiv/REVISION_NOTES.md) maps every retained theorem, corollary and analytical appendix to the original 22-page PDF.

1. Reconstructed full editable TeX and a separate bibliography; standardized author metadata, clickable enduring contacts and the fixed revision date.
2. Retained the complete integrated-response and radiation-efficiency proof, noncommuting tensor identity, exact fixed-resource gap, full ball radiation spectrum and linear size estimate without a multipole cutoff.
3. Retained the complete positive-extinction resolvent argument, explicit current optimizer, infinite-spectrum endpoint argument, feasibility conditions, forward-cap correction and combined envelopes. Kept the distinction between an exact current relaxation and a physically attainable two-illumination optimum.
4. Retained the exact-Maxwell anisotropic-sphere proof and coefficient **160/2071**, passive causal realization, conditional six-component extension and analytical spectral-tail bounds.
5. Restored conjugation bars in the time-reversed polarization and typeset the diameter-to-enclosing-radius factor unambiguously as **sqrt(3/8)**. Corrected reconstructed alignment row breaks and clarified that the scattered field is outgoing.
6. Distinguished the general complex-polarization cubic example from the companion real-linear quartic refinement, and replaced obsolete wording that the latter remains wholly open.
7. Removed the research-continuation subtitle, draft headers, status ledger, archive/replay promises, numerical certificate and discrete-dipole tables, and historical cross-paper/formal-audit discussions from the research narrative. Exact analytical coefficients and all retained theorem proofs remain.
8. Replaced the novelty table with direct attribution to established response, radiation, modal and cross-source bounds. Kept 15 relevant external references and added the unpublished quartic companion without inventing a public identifier.

## Compact Maxwell cross-sections manuscript

The new title is **Finite-Aperture Localization and Dipolar Bounds for Reciprocal Absorption Asymmetry**. [REVISION_NOTES.md](papers/compact-maxwell-cross-sections/arxiv/REVISION_NOTES.md) records the mapping from the original 24-page PDF and the overlap with the prescribed-extinction result.

1. Reconstructed full editable TeX and bibliography; standardized author metadata, clickable enduring contacts and the fixed date.
2. Refocused the title, abstract and introduction on the fixed-stack finite-aperture theorem, explicit square-aperture rate and complete dipole equality/radiation dressing.
3. Retained full proofs of the dimensional dipole bound, passive reciprocal equality tensors, active-block radiation removal, nonnormal commutator identity and directivity obstruction. Distinguished point-model feasibility from a local dielectric realization.
4. Added a complete weak vacuum uniqueness argument to support the volume-to-Maxwell converse. Made positive support volume explicit; clarified weak representatives, outgoing scattered fields, measurable-support approximation, distributional contact terms, all-angle optical flux and exact reciprocal extinction. Restored two missing TeX spacing-command backslashes in the power identities.
5. Retained the full mixed Fourier localization proof, with the transform applied before material-aperture restriction. Kept the grazing singularity in the integrable estimate and the complete square-window derivative and nonoptimal **O((kR)^(-1/3))** rate proof.
6. Retained the exact planar construction, positive-loss regularization and ordered aperture limit under fixed upper material caps. Kept dispersion/oscillator and resource limitations explicit.
7. Replaced the obsolete claim that prescribed nonzero extinction remains unresolved with the precise statement that it is addressed by the stronger companion manuscript. Disclosed that the unrestricted supremum is weaker and should not be counted as a separate discovery.
8. Removed unsupported numerical-release promises, DDA tables, audit-process narration, status badges, old build paths and auxiliary scalar/archive examples not needed by the retained proofs.
9. Replaced the prior-art table with source-cited related work, added direct polarization precedents, and used 16 relevant references, including the unpublished prescribed-extinction companion. No arXiv identifier, DOI, public repository availability or transferred formal certificate is invented.

## Recovered originals and repository navigation

- Copied the previously missing quartic manuscript, quartic audit and fixed-resource manuscript PDFs from the local `GPTRESEARCH` folder; verified matching SHA-256 hashes. Recorded them in [RECOVERED_PDFS_2026-10-14.csv](archive/RECOVERED_PDFS_2026-10-14.csv).
- Added [RECOVERY_STATUS_2026-10-14.md](archive/RECOVERY_STATUS_2026-10-14.md) rather than rewriting the earlier bounded-import report.
- Updated the root and paper landing pages to distinguish current editable revisions from preserved historical originals. Updated reproduction instructions.
- Added [ARXIV_SUBMISSION.md](ARXIV_SUBMISSION.md) with source-upload locations, account/contact guidance, local build instructions and the remaining author-controlled submission steps.
- Reconstructed and revised fixed-resource and compact-Maxwell manuscripts as well, with separate source packages and detailed revision notes. Distinguished editable packaging from a claim of independent scientific novelty; compact-Maxwell's main unrestricted supremum is weaker than the prescribed-extinction theorem.
- Worked in the user-selected `C:\Users\ZJJ\Desktop\oq7-prescribed-extinction` checkout after pulling main. The preferred `D:\oq7-papers` clone documented by the collection is absent on this host. No external research-folder file was edited.

## Build and verification

Added `scripts/build-arxiv.py` to compile each manuscript in a fresh ignored directory with shell escape disabled and create a clean deterministic source ZIP. It checks author order, enduring contacts, fixed dates, upload filenames, figure dependencies and resolved references. ZIPs contain compilation inputs and supplied ancillary evidence, excluding compiled manuscript PDFs, logs, scratch files and revision notes. Each manuscript has a machine-readable `BUILD_VERIFICATION.json`.

The final PDF page counts, visual checks, source-package checks and preserved-collection integrity result are recorded in [ARXIV_VERIFICATION.json](ARXIV_VERIFICATION.json). The local TeX Live version is 2024; no actual arXiv server compilation or submission is claimed. AI-assisted mathematical checks and PDF compilation do not constitute completed human peer review or a certification of scientific priority.

The complete changed-file list, old and new hashes where applicable, and file dispositions are in [ARXIV_CHANGE_INVENTORY.json](ARXIV_CHANGE_INVENTORY.json). `SHA256SUMS` is refreshed for the current repository files while the historical origin and relocation maps remain unchanged.
