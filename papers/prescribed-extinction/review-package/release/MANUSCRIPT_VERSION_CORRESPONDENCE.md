# Manuscript version correspondence

Audited formal authority: commit `686402a6c2d63820828729cc7ab02504632e3fe7`, tree `580737ccf6557102d601894145cc0229ae1f83e3`; declaration `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement`.

| Manuscript | Content identity | Main statements |
|---|---|---|
| Audited October 11 specification, 19 pages | SHA-256 `3d9775d849234e828370d7c96d8bdcdd574beb6831a7906ea6b7706579868710`; exact copy in evidence/manuscripts/ | Theorem 1.1 and Lemma 1.2, PDF page 3 |
| Newer publication baseline, 16 pages | SHA-256 `aa3a3fdb569a69d9fef82ecd54fe94d346f3723a0e65f597c24ac18ee3e1890d`; preserved in evidence/publication-baseline/ | Theorem 4.1 and Lemma 4.2, PDF page 4 |
| Release manuscript | manuscript/main.tex and manuscript/paper.pdf; exact identities in SHA256SUMS | Same Theorem 4.1 and Lemma 4.2; formal-status prose updated |

## Precise main-statement mapping

| Audited October 11 content | Newer publication content | Assessment |
|---|---|---|
| k>0, P>1, Q>0, every E_*>0, every 0<epsilon<1 | Identical quantified parameter ranges in Theorem 4.1 | No substantive change |
| Two adjacent homogeneous anisotropic dielectric layers; common finite square aperture in vacuum | Section 3 and Theorem 4.1 explicitly use finite positive R,h,d and the two-layer square-aperture class | Same formal geometry; more explicit positivity and coordinate convention |
| Relative permeability I; transpose reciprocity; I <= Re_H epsilon <= PI; 0 < Im_H epsilon <= QI, Eq. (3) | Same material conditions, Eq. (2) | No substantive change; no common positive loss floor added |
| Opposite unit-amplitude e_y-polarized plane waves along +/-e_z, Eq. (1) | Same Eq. (1), local L2 distributional Maxwell model in Eqs. (3)-(4) | Same frequency, illumination and normalization |
| X_+=X_-=E_* exactly; 1-epsilon<Gamma<1, Eq. (4) | Same equalities/inequalities, Eq. (9) | No approximate target substituted |
| sup at fixed X=E_* of Gamma =1, and sup of absolute absorption difference =E_* | Identical suprema over explicit C_(k,P,Q,E_*), Eq. (10) | Same class and two sharp values |
| Lemma 1.2: X>0 implies Gamma<1 for each body | Lemma 4.2: X>0 implies 0<=Gamma<1; both suprema explicitly nonattained | Nonnegativity is made explicit; already follows from the absolute-value definition and positive denominator. Not a stronger physical claim |
| Gamma=absolute absorption difference/X=absolute scattering difference/X; X=A+S, Eq. (2) | Work, far field, energy balance and Gamma are separated into Eqs. (5)-(8) | Same area normalization and all-angle, both-polarization scattering |
| 'The pair (1)' interpreted as physical outgoing fields | Unique outgoing weak fields stated explicitly; a.e. uniqueness and canonical radiating representative explained | Clarification of the F2/F3 content already covered by the completed final audit |
| Every selected dimension/coefficient finite, no shared bounds on aperture/thickness/volume/resources or lower loss | Same limitations and explicit nonattainment | No fixed-resource, bandwidth or all-isotropic claim added |

The old and new strictness proofs use passivity, continuity of the far field and the forward optical theorem. The formal proof can instead use positive absorption at positive extinction. These are compatible routes to the same conclusion; identical proof presentation is not required by statement correspondence.

## Changes outside the main statement

The newer paper is a focused reorganization of the prescribed-extinction result. It makes the weak equations, radiation normalization, canonical representatives and scalar inverse argument explicit; presents the uniform aperture reasoning in a Weyl/Fourier organization; adds a geometry figure and expanded attribution; and separates the construction, aperture limit, exact tuning and positive-loss regularization into Sections 6-8. The formal localization proof has a different physical-space/L2 organization.

The October 11 specification's Section 6 contains distinct joint-resource and small-size variational/asymptotic results, and Section 7 numerical/algebraic diagnostics. These are not part of the audited Theorem 1.1/Lemma 1.2 and are not carried forward as formalized results of the focused publication paper. Causality/dispersion observations remain outside the main formal theorem. Removing those separate subjects is a scope change of the manuscript, not a weakening of its prescribed-extinction theorem.

A specific proof-presentation clarification is the Fourier domain of the windowed residual. The October 11 page-6 Eq. (26) uses the symbol H_R,theta in its Fourier formula. The newer Section 7.2, Eqs. (35)-(37), explicitly distinguishes the unrestricted observation field tilde-H on R^2 times (0,L) from its restriction H to D_R and takes the transverse transform before aperture restriction. This avoids treating restriction as if it commuted with Fourier transformation; only the low-frequency part uses global Plancherel. It is a meaningful domain/notation clarification of an intermediate argument, not a change to the main theorem. The October 11 Theorem 3.1 (page 5) and newer Theorem 7.1 (page 8) retain the same angle-uniform normalized current and power limits at fixed positive active losses. The newly explicit uniqueness appendix and reorganized planar-amplitude appendix are expository additions; the completed main audit does not certify every line of those presentations.

The final audit's semantic PASS applies to the October 11 main theorem/lemma for the encoded two-layer class. This release's comparison transfers that main-statement correspondence to the newer paper. It does **not** certify every intermediate lemma, numerical constant, Weyl-fiber proof paragraph, appendix argument or expository presentation. S1 retains declaration-by-declaration distinctions among direct formal statements, consequences and differently organized proofs.

## Release changes

MANUSCRIPT_CHANGES.diff records every change from the newer publication baseline. Only formal-status paragraphs were edited: the final-commit audit is incorporated; audit positivity lemmas are acknowledged; historical pending-review metadata is contextualized; same-kernel replay and human peer review are distinguished. All scientific theorem, lemma, proposition, corollary and equation environments are unchanged. The build retained 51 numbered equations, 20 bibliography entries and the same geometry assets.
