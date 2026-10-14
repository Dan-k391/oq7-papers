# Generalized manuscript reconstruction and revision

14 October 2026

The current paper is **Reciprocal Absorption Asymmetry: Sharp Channel Tradeoffs and Dielectric Thickness Asymptotics**, by Daniel Wang (McMaster University) and Junjie Zheng (Columbia University), in that order. Lasting contact addresses are `denialk391@gmail.com` and `zjj2785@gmail.com`.

This is a new editable reconstruction and substantial revision of the 41-page [original PDF](../manuscript/OQ7_generalized_research_2026-10-10.pdf), SHA-256 `3f01036ff6bc99939b1f2b1a8a205ac4e755188930535db1336d841ca7d377bf`. Its original editable TeX is unavailable. The user authorized reconstruction from the PDF. The original PDF, extracted text, historical research records and formal sources remain unchanged.

## Results and section mapping

| Original material | Revised disposition |
|---|---|
| Section 1 novelty and audit tables | Concise introduction and related work; no first-priority claim |
| Section 2 established two-port optimization | Section 2 proves feasibility and the sharp ceiling; redundant degeneracy classifications and literature-elimination algebra removed |
| Sections 3–4 scalar model and resource floor | Section 3 retains the complete Gram, transfer, complex-comparison, Fourier-moment, tangent and material-floor arguments |
| Theorem 5.1 and Corollary 5.2 | Theorem 4.1 and Corollary 4.2 retain the exact-target thickness asymptotic and minimum-thickness consequence |
| Section 5 matching construction | Section 4 retains the complete accumulated-product expansion, determinant coefficient, bounded-index matching networks, real implicit-function argument and passage to every large thickness budget |
| Sections 6.1–6.2 channels and passivity | Section 5 retains reversal, normalization, the sharp extinction parabola and overlap bound |
| Section 6.3 golden-ratio optimization | Removed as an auxiliary consequence of the established scalar feasible set |
| Sections 6.4–6.5 vector construction and beams | Section 7 retains the exact tensor-layer construction, arbitrary real cap and finite-power retuning argument |
| Section 6.6 resource counterexamples | Essential tensor determinant counterexample retained; auxiliary absorption-ratio discussion removed |
| Theorem 7.1 and its proof | Theorem 6.1 retains all branches, canonical compression, positive-matrix certificate, middle-branch equality classification, outer equality constructions and continuous transitions |
| Section 7 exact rational example | Remark 6.2 retains the exact improvement over the minimum of separate bounds |
| Section 8 numerical and audit records | Removed from the scientific narrative; original records preserved without claiming an unavailable numerical replay |
| Section 9 status and failed-shortcut tables | Concise scope and conclusions in Section 8 |
| Appendix A analytic bridges | Integrated into the relevant proofs, including the explicit accumulated-product remainder |
| Appendix B formal/build inventory | Replaced by a concise statement of the historical verification scope; no complete formal-verification claim added |

## Scientific corrections and scope

The misleading description of “finite geometry” is corrected: finite layer thicknesses and material coefficients do not make the laterally infinite planar medium a compact scatterer. This remains true for finite-power beam illumination. The revised abstract and conclusions distinguish dimensionless complete-channel powers, infinite planar materials, finite-power beams and compact three-dimensional cross sections.

The thickness theorem keeps fixed transmitted power `T`, mean absorptance `a`, integrated imaginary permittivity `M`, real and imaginary material caps, and strictly active targets. Its construction permits growing layer count and shrinking lossy slices. No minimum feature size, finite material catalogue, degenerate boundary target or bandwidth conclusion is added. The negative transfer exponents used in the product algebra are explicitly distinguished from the positive physical spacer thicknesses.

The overlap-envelope equality operators are abstract reciprocal contractions. Their construction is not a local Maxwell realization at nonzero overlap. Established outer passivity/overlap bounds and polarization mechanisms are attributed to prior work, while the complete scalar optimization and middle-branch certificate remain the focused mathematical claims. Scientific priority is not certified.

## Bibliography and presentation

- Rewrote the title, abstract, introduction, section order and conclusions around the two principal results.
- Added author affiliations, enduring emails, matching PDF metadata and a fixed date; omitted student status and did not infer departments or ORCIDs.
- Corrected Kuang–Zhang–Miller's Optica page range to **1746–1757**, checked in the [author-hosted primary PDF](https://millergroup.yale.edu/sites/default/files/files/2020_12-Kuang.pdf).
- Completed Barreaux's author list and Li/Kim's name metadata. Added the established Khurgin 2021 polarization-mechanism comparison.
- Reduced the 24 historical references to 21 references used by the revised presentation: removed the metasurface precursor, incomplete Martin comparison and implementation references, and added Khurgin 2021.
- Removed audit badges, missing-project counts, engine-path troubleshooting, process history, numerical tables and formula-only plots. Complete supporting analytic arguments remain in the source.
- Corrected a reconstruction typo in the transmission-phase factor to `r_L r_R (conjugate(t))^2`.
- Kept a concise AI-assistance disclosure and precise verification scope.

## Review and validation

The mathematical review and symbolic cross-checks were AI-assisted. Checks covered the scalar feasibility/ceiling algebra, complex comparison, capped Fourier moment and all-profile floor, cubic matrix coefficient, accumulated-product correction, exact target-matching Jacobian, all-large-thickness argument, joint certificate determinant and vanishing entry, parameter monotonicity, equality operators and branch transitions. No invalidating central constant error was identified in these checks. This is ordinary mathematical review, not completed human peer review or a priority certificate.

The historical formal supplement covers selected algebraic and finite-channel statements and a generic trace certificate. It does not certify the scalar physical floor/thickness theorem, canonical compression or full overlap envelope. The prescribed-extinction formal audit also does not certify these separate results. No Lean source was read, edited or executed in this task.

The final source uses standard pdfLaTeX/BibTeX packages with no external figures or shell escape. The locally built paper is 16 pages, with resolved references/citations and no overfull boxes. The final rendered PDF, source-package hashes and checks are recorded in `BUILD_VERIFICATION.json` and the collection's `ARXIV_VERIFICATION.json`. The actual arXiv server environment has not been tested.
