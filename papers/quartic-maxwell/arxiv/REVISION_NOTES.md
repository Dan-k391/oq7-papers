# Quartic manuscript revision, 14 October 2026

This is a new editable reconstruction and substantial revision. It is not the recovered original TeX source. Historical manuscripts, original audit reports, frozen formalization and archives were not edited.

## Exact source record

- Original 17-page manuscript: `C:/Users/ZJJ/Desktop/GPTRESEARCH/OQ7_quartic_Maxwell_2026-10-10.pdf`, SHA-256 `576478ba88fd374e724b96e07c5e3e1648485cd163dc4d8ba9cd0b3ef52eac62`.
- Original 15-page adversarial audit: `C:/Users/ZJJ/Desktop/GPTRESEARCH/OQ7_quartic_adversarial_audit_2026-10-10.pdf`, SHA-256 `178914944734ddcf14c76a363b952afec901c57ca56f32b2f503c90c1d98c59b`.
- The October 11 prescribed-extinction continuation, SHA-256 `3d9775d849234e828370d7c96d8bdcdd574beb6831a7906ea6b7706579868710`, contains additional class-uniform sixth-order and variational-supremum claims. They are **not imported into this revision**.

## Claim disposition

| Historical claim | Revised location | Disposition |
|---|---|---|
| Uniform exact quartic inequality, original Theorem 1.1 | Theorem 1.1 and Section 2 | Bound, constants and arbitrary measurable-support scope retained; susceptibility measurability made explicit. |
| Heterogeneous finite-sphere coefficient and quantitative remainder, original Theorem 1.2 | Theorem 1.2 and Section 4 | Complete isolated-moment, interaction, noncancellation and full-Maxwell remainder proofs retained, including the original rational constants and intervals. |
| Every-resource-class sharp exponent, original Theorem 1.3 | Theorem 1.3 and Section 5 | Complete homogeneous unequal-sphere first-interaction and all-multipole error proof retained. No maximizing pattern or optimal prefactor claimed. |
| Fixed-pattern coefficient, original Theorem 4.1 | Theorem 3.1 | Exact static volume-response formula and fixed-pattern O(t^6) proof retained. No class-uniform O(t^6) inference. |
| Weak Maxwell equivalence on arbitrary measurable supports | Section 2 and Appendix A | Canonical smooth exterior representative and outgoing scattered fields specified; entire-vacuum uniqueness proof included. |
| Numerical Mie diagnostics | Not reproduced in the new paper | Historical computations remain evidence in their original record. No numerical source archive was recovered or rerun for this revision, and no fresh numerical reproducibility is claimed. The complete analytic coefficient and remainder proofs are included. |
| Prior-art and workflow/audit narration | Section 6 and concise verification disclosure | Equation-level comparison added; research-process narration and unverified archive/replay promises removed. |

## Mathematical review for this reconstruction

Ordinary independent review checked the dyadic eigenvalues and Schur constant, loss coercivity and surjectivity, whole-sphere radiation normalization, reciprocity, denominator cancellation as volume tends to zero, coefficient scaling and absence of a fifth-order remainder, both sphere coefficient certificates and their explicit constants, minimum-radius conversion, and passive Lorentz examples. No new invalidating gap was identified after the explicit measurable-coefficient correction. This is AI-assisted ordinary mathematical review, not Lean/kernel verification or completed human peer review. The prescribed-extinction formal audit does not apply to these quartic claims.

The original audit's statement defect is addressed by explicitly requiring `chi in L-infinity(D; C^(3x3))`. Pointwise algebraic caps alone do not establish measurability. The new title makes uniformity the central contribution; sharpness refers to the exponent and not to the prefactor.

## Primary sources inspected for revised attribution

- Sounas and Alù (2014): [official publisher abstract](https://opg.optica.org/ol/abstract.cfm?uri=ol-39-13-4053), supporting reciprocal extinction and loss-enabled directional redistribution. Only this general attribution is made; complete four-page priority equivalence was not established.
- Hopkins et al. (2015): [publisher article](https://doi.org/10.3390/photonics2020745), with publisher-provided full text inspected through [ResearchGate](https://www.researchgate.net/publication/280528057_Fano_Resonance_Enhanced_Nonreciprocal_Absorption_and_Scattering_of_Light). Equations (12)–(15), the transverse Green coupling, and Figure 3's opposite real-linear illumination were inspected. The new scalar comparison is our algebraic reduction, not a newly attributed published theorem.
- Ammari–Deng–Millien: [arXiv:1412.3656v1 full text](https://arxiv.org/html/1412.3656v1), Theorem 5.8, Eq. (5.32). The fixed-smooth quartic upper order is explicitly identified as an inference from that expansion under zero magnetic contrast and fixed positive loss. It is not represented as their explicit theorem or as uniform over changing measurable supports.
- Schab et al. (2020): [primary arXiv PDF](https://arxiv.org/pdf/2009.08502), Section 3.1, radiation-to-loss eigenvalue discussion. The bibliography uses the actual authors Austin Rothschild and Kristi Nguyen.
- Molesky et al. (2022): [primary arXiv record](https://arxiv.org/abs/2102.10175), supporting only the general multi-input T-operator framework attribution. No uninspected equation-level equivalence is claimed.

These sources establish close precedents for effects and methods. They do not certify novelty of the exact uniform quantitative theorem. The Mann–Alù 2023 contribution and other incompletely accessed priority leads in the historical audit remain unresolved; omission of those leads from the paper's small working bibliography is not a claim of their irrelevance or absence.

## Authorship and build

Author order and current affiliations follow the user's instruction: Daniel Wang (McMaster University), then Junjie Zheng (Columbia University). Personal contact addresses are `denialk391@gmail.com` and `zjj2785@gmail.com`. No department, degree status or ORCID was inferred. Manuscript date: 14 October 2026.

The source uses standard pdfLaTeX packages, a separate `references.bib`, and no external figures, numerical datasets or shell escape. Build intermediates are generated in `.local/quartic-build/`. Compilation with TeX Live 2024, BibTeX and repeated pdfLaTeX succeeded; the resolved 13-page output has no undefined references/citations or overfull/underfull box diagnostics. The expected epstopdf warning reports that shell escape is disabled; no conversion is needed. Root handles final PDF rendering, visual QA and source packaging.
