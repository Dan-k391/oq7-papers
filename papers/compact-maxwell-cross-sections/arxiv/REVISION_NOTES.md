# Compact Maxwell manuscript revision - 14 October 2026

This is a new editable reconstruction, not an alteration of the historical PDF. The source is `../manuscript/OQ7_compact_Maxwell_cross_sections_2026-10-10.pdf` (24 pages; SHA-256 `eb85dd064e8dd2410c0b6f88cd6463c2d0700a3b35dcc307cd152cf8f3c4cd6a`). The Desktop/GPTRESEARCH original and the repository manuscript copy remain unchanged. No Lean source was read, edited or used as a verification certificate for this revision.

## Publication focus and overlap

The revised title is **Finite-Aperture Localization and Dipolar Bounds for Reciprocal Absorption Asymmetry**. The focus is the fixed-stack material-aperture limit, its explicit square-aperture error, and complete dipole equality/radiation dressing. The unrestricted compact unit supremum remains fully proved, but it is weaker than the companion prescribed-extinction theorem for the same two-layer class. The paper now discloses this overlap and cites the companion as an unpublished manuscript, without inventing an arXiv identifier, DOI or public URL. Five edited documents should not be represented as five independent discoveries.

The original statement that prescribed nonzero total extinction is unresolved has been replaced by the precise limitation that it is not proved by this fixed-stack construction and is addressed in the companion. Exact total-extinction tuning would require angle-uniform normalized localization beyond the theorem proved here. The present proof and rate are not claimed uniform as the loss floor vanishes or thickness diverges.

## Claim and section mapping

| Historical material | New treatment |
| --- | --- |
| Abstract, Section 1 and Theorem 1.1 | Reframed introduction; definitions and strictness in Section 2; complete unrestricted-supremum construction in Section 7 |
| Section 1.1 optical-theorem/directivity obstruction | Retained with proof; incidence labels H/L avoid confusion with layer thickness h |
| Section 2 dipole normalization and Theorem 2.1 | Retained in Section 3, including complete six-vector passivity, area factor and endpoint/equality scope |
| Section 2.2 equality tensors, bare response and commutator identity | Retained with algebraic proof; clarified active-block inverse and equivalent full-space radiation dressing |
| Section 2.2 auxiliary scalar golden-ratio and electric-only archive example | Removed; neither supports the retained central proofs, and inaccessible archive formulas are not promised |
| Sections 3.1-3.3 Green, volume and planar model | Retained and reorganized into Sections 4-5 |
| Original converse Green-representation assertion | Expanded into a complete entire outgoing weak vacuum uniqueness proof; Maxwell-volume equivalence is now proved explicitly |
| Section 3.4 grazing-frequency localization | Retained in Section 5; Fourier transform explicitly acts on the unrestricted strip before aperture restriction |
| Section 3.5 square cutoff and nonoptimal rate | Retained with full derivative, Fourier, residual and rate proofs in Section 6 |
| Sections 3.6-3.7 planar construction, positive loss and compact supremum | Retained with full ordered-limit proofs in Section 7 |
| Section 4 dispersion/resources | Retained concise passive Lorentz construction and oscillator energy identity in Section 8; fixed-stack resource limitations remain explicit |
| Section 5 DDA/numerical experiments and audit narratives | Removed from the research PDF; no recovered numerical programs, JSON files, numerical certification or fresh solver replay is claimed |
| Section 6 prior-art audit table | Replaced by concise source-cited related work in the introduction |
| Section 7 open-problem list and Appendix A old build/archive promises | Replaced by current precise scope and conclusion; archived status and obsolete scripts are not publication evidence |

## Corrections and clarifications

- Added Daniel Wang first (McMaster University) and Junjie Zheng second (Columbia University), with their lasting personal email links, using the common five-paper author format.
- Added descriptive PDF metadata and a fixed revision date of 14 October 2026.
- Defined weak fields, almost-everywhere uniqueness and canonical smooth exterior representatives; established existence, Maxwell equivalence, optical flux and reciprocal extinction by ordinary arguments.
- Made positive support measure explicit for the generic positive-extinction assertion, distinguished outgoing scattered fields from the incident-plus-scattered total field, and specified the smooth-density extension through a larger ball for arbitrary measurable supports.
- Kept the distributional static contact term and the longitudinal Weyl term `-I`; no pointwise Hessian substitution or global Plancherel through the grazing circle is used.
- Distinguished the geometric square from its scattering cross section, and kept fixed-frequency dimensional factors in the nonoptimal rate constants.
- Distinguished passive reciprocal point-model feasibility from physical local-dielectric realization; the dipole directivity ceiling is not imposed on arbitrary large compact bodies.
- Retained exact material caps and the order finite planar choice, positive isotropic loss, then aperture enlargement. No fixed total extinction, uniform positive loss floor, bounded resources or bandwidth was added.
- Removed novelty labels, audit success badges, agent workflow, original archive-preservation claims in the scientific text, unsupported numerical-file availability promises and old source-path commands.
- Added direct polarization-mechanism citations (Armitage 2014 and Khurgin et al. 2021), retained known dipole precedents and fixed source metadata from primary publisher/institutional records where checked.
- The new bibliography has 16 entries: obsolete DDA and small-sphere completion citations and unrelated bound comparisons were removed; the unpublished companion and direct mechanism precedents were added.

## Mathematical review and verification limits

Ordinary source review checked the dipole dimensional factor, orthogonality of transformed reversed inputs, positive defect/equality tensors, bare radiation dressing, nonnormal commutator identity, co-polar directivity ceiling, weak-volume bridge, light-circle integrability, square-window derivatives and the ordered supremum limits. No confirmed false retained central statement was found. This does not certify scientific priority, independently implemented kernel checking, numerical continuum accuracy or human peer review. Final compilation and rendered layout checks are recorded by the parent publication build.

## Files and build

`main.tex` and `references.bib` are the editable source. Compile with shell escape disabled; bibliography generation and two final LaTeX passes resolve citations and references. Build intermediates belong in the ignored `.local/` tree. The parent task generates `paper.pdf` and the source ZIP and checks the final render. Nothing has been published, submitted or uploaded online.

The revised source compiled successfully to 13 pages on 14 October 2026 with `pdflatex -no-shell-escape`. The log had no overfull or underfull boxes, undefined citations or references, multiply defined labels, or rerun requests. The only package warning states that shell escape is disabled. Text extraction confirms the corrected power identities contain no literal `qquad` text. These checks concern the current editable revision; they do not alter verification claims for the frozen original or its proof project.
