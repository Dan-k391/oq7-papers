# Generalized-research paper: mathematical audit

Date: 14 October 2026. Auditor: AI-assisted (Claude), commissioned by Daniel Wang. This is not human peer review.

**Audited version:** `papers/generalized-research/manuscript/OQ7_generalized_research_2026-10-10.pdf`, 41 pages, SHA-256 `3f01036ff6bc99939b1f2b1a8a205ac4e755188930535db1336d841ca7d377bf`.

This is the "Paper A" of the historical OQ7 mission (`historical-notes/projects/oq7-mission/`). The equations were read from the PDF, with matrices confirmed by layout-mode extraction; see G-3. The audit followed the main paper's three strands. Prior records were consulted only for the reconciliation at the end.

## Claim register and dependencies

| Claim | Depends on | Verdict |
|---|---|---|
| Props. 2.1–2.2, two-port feasibility and envelope (stated KNOWN, Guo–Fan) | determinant criterion; identity (10) | Correct |
| Gram identity (20), coating invariant (21) | Wronskian; flux | Correct; covered inside the Lean proof of Thm 5.1 |
| Lemma 4.1, complex modulus comparison | Sturm/Duhamel for ρ = \|s\| | Correct |
| Lemma 4.2, capped Fourier moment | positive-part (bathtub) inequality | Correct |
| Lemma 4.3, cell determinant | sin² identity; Minkowski det^{1/2} superadditivity | Correct |
| Lemma 4.4, convexity and global tangent | H′ = 2f sin 2u | Correct |
| Thm 4.5, resource floor and lim inf (29) | Lemmas 4.1–4.4 | Correct |
| **Thm 5.1, sharp exact-target asymptotic** | Thm 4.5, tangent bound (33), construction §5.2–5.4 | **Correct; FULLY KERNEL VERIFIED as `OQ7.theorem51` (G-1)** |
| Cor. 5.2, asymptotic minimum thickness | Thm 5.1 and monotonicity of D*(L) | Correct (ordinary) |
| Prop. 6.1, Thm 6.2, X − X²/4 channel bound (stated KNOWN) | single-input passivity disk | Correct |
| Pair-overlap bound (49) | trace of B against uu† − vv† | Correct (the bound is √(1−ρ²); plain extraction drops the root) |
| §6.3 scalar envelope (50); Thm 6.3, γ₂ = √(10√5−22) | real-contraction reduction, h′(q) ∝ 1−q−q² | Correct |
| Physical approach to γ₂ via Thm 5.1 and a phase slab | Thm 5.1 at target (q⁴, 4q−2) | Correct; D₀/(2(1−q²)) = γ₂ verified |
| Thm 6.4, two-layer vector construction | exact half-wave plate; slab formulas (54); 4-port (55) | Correct |
| Cor. 6.5, finite-power beams with exact extinction | continuity in κ; IVT in plate angle | Correct (ordinary) |
| §6.6, determinant-floor and ratio counterexamples | PSD absorption matrix with zero diagonal | Correct |
| **Thm 7.1, prescribed-overlap three-branch envelope** | compression B² ⪯ Q ⪯ I; certificate (63)–(65); outer branches | **Correct** |
| §7.4 rational example | Thm 7.1 | Correct; Lean replay passes |

## Audit A: analytic re-derivation (selected)

- **Prop. 2.2.** F(x) = (y+T)² − (1−2a) with y = √(b²−x²). Matrix (8) attains the envelope with det(I−SᵀS) = 0.
- **Lemma 4.1.** Writing s = ρe^{iθ} gives ρ″ = ρθ′² − k²pρ = j²/ρ³ − k²pρ, hence ρ″ + K²ρ ≥ 0 for p ≤ P. Comparison with sin(Kh)/K follows by variation of constants with a nonnegative kernel on [0, π/K].
- **Lemma 4.2.** ∫max(cos θ − cos λ, 0) dz = (sin λ − λ cos λ)/K over one period. The mass term cancels at μ = Qλ/K.
- **Lemma 4.3.** ∫∫_{x<y} qq sin²(K(y−x)) = (m² − \|∫qe^{2iKx}\|²)/4. Inserting it in (20) gives det A_J/T ≥ (Q²/P²)(u² − sin²u).
- **Theorem 4.5.** f(u) ≥ 4u⁴/(3π²) on [0, π/2] gives (27). The asymptotics f ≈ u⁴/3 and n_f ≈ k√P L/π give (29).
- **Tangent bound (33).** −F′(x₀) = 2x₀s/y₀, so Tc ≤ (sx₀/y₀)(D₀−D), i.e. D₀ − D ≥ αc.
- **Construction (§5.2–5.4).** The cubic coefficient C₃ = [A,[A,B]]/24 + [B,[A,B]]/12 = (1/12)[[0, −Q],[Q(P+2iQ), 0]] was recomputed and agrees with (36) as printed. The quantity m²c_m tends to g₀⁴/(3Q²), reproducing the Table 2 column to 10⁻⁸.
- **Theorem 6.3.**
  - The real symmetric comparison matrix is a contraction by the reverse triangle inequality.
  - The step √(1−c²)/(1−qc) ≤ 1/√(1−q²) is equivalent to (c−q)² ≥ 0.
  - h(q) = 4q²(1−q)/(1+q) peaks at the golden ratio.
  - The equality matrices (52) have a singular PSD defect.
- **Theorem 6.4.**
  - The plate eigenvalues 1 and 4 have phases π and 2π, so the plate is exactly reflectionless with H = −V, and its normalized transmission is V.
  - S = [[R, DH],[HD, HRH]] is symmetric and passive. It gives A_L = 0, A_R = (1−t²)A_x and X_L = X_R = 2(1−t).
  - A_x = kη∫\|E_x\|² holds, and A_x(1/m, m²) → 1. The m = 128 values in the text are reproduced to 10⁻¹⁰.
- **Theorem 7.1.**
  - B² ⪯ Q ⪯ I follows by discarding the imaginary output.
  - tr(WB) is the forward overlap, and \|A(a)−A(b)\| = 4pq\|Q₁₂\|.
  - The certificate chain tr(WB) ≤ r₀ + ν(h−h₀) uses tr H = tr(HQ₀) and tr(WB₀) = 2tr(ZB₀²).
  - The identities B₀Z + ZB₀ = W, det Z = D(ρ−c)/(16c(1−c²)) > 0 and H = δO diag(1,0)Oᵀ were checked on 300 random (ρ, c).
  - r₀(c) is increasing.
  - The witnesses of all three branches attain Δ_ρ, and the branches are continuous at r = ρ/2 and r = ρ.

## Audit B: counterexamples and edge cases (diagnostics, `checks/`)

The searches were adversarial. None found a violation.
- 4,000 random reciprocal two-ports against Prop. 2.2.
- 20,000 random two-ports against γ₂.
- 1,500 random reciprocal contractions (n = 2–4) with random symmetric-unitary references, against Thm 6.2 and extinction reciprocity.
- 2,500 random complex symmetric contractions plus 60 hill-climbs, against Thm 7.1.
- Lemma 4.1 on 120 random capped stacks up to 0.999π/K. The manuscript sampled only up to π/(2K).
- Lemma 4.4 on dense grids.

The excluded edges T = 0, a = 0, a = (1−T²)/2 and P = 1 are excluded by both the manuscript and `ScalarEnvelope.ActiveTarget`.

## Audit C: model fidelity

- **Scalar model.** It is normal incidence with nonmagnetic layers in identical vacuum exteriors, and all layers count toward the thickness. The Lean model uses closed-form homogeneous-layer transfer matrices in the state (E, E′/(ik)). I re-derived these from E″ + k²εE = 0 with E and E′ continuous. Wave-basis boundary formulas: r_L = −K₁₀/K₁₁, r_R = K₀₁/K₁₁, t_R = 1/K₁₁, t_L = det K/K₁₁. Absorptances: 1 − \|r\|² − \|t\|². This is the only bridge between the Lean statement and the ODE (17). The bridge is a standard ordinary computation and is not formalized.
- **Normalization.** The channel results are dimensionless powers per unit incoming power. The paper correctly warns that they are not compact-body cross sections, and that the Thm 6.4 structure is laterally infinite.

## Classified issues

| ID | Class | Issue | Effect |
|---|---|---|---|
| G-1 | Verification-record error (not mathematical) | The abstract, §8.5 and Appendix B say `OQ7.theorem51` was "absent" and Thm 5.1 "unverified in Lean". The declaration is preserved in `historical-notes/projects/oq7/` and, byte-identically, in `papers/prescribed-extinction/formalization/OQ7/` at tag `audited-686402a`. Replayed today, its type is exactly the manuscript's Thm 5.1, its axioms are standard, and `leanchecker --fresh` passes | Thm 5.1 is FULLY KERNEL VERIFIED, conditional only on the ODE bridge in Audit C. The arXiv revision (`../arxiv/main.tex`, l. 660) repeats the understatement and should be corrected |
| G-2 | Unrecoverable evidence | The 43-theorem Lean 4.19 supplement of Appendix B is not in the repository | Its LEAN-VERIFIED claims cannot be credited. The rational §7.4 certificate is separately covered by the replayed `OQ7Mission.RationalOverlap` |
| G-3 | Audit hazard (not a paper error) | Plain `pdftotext` and the stored `.txt` list matrix entries column by column. Read row-wise, (55), (36) and [A,[A,B]] look wrong | Layout-mode extraction confirms the printed matrices are correct |
| G-4 | Scope | Cor. 5.2, Thm 6.3's physical approach, Cor. 6.5 and the full Thm 7.1 are ordinary proofs only | No defect found |
| G-5 | Priority lead | Sounas & Alù, PRB letter (Feb 2026), doi:10.1103/mb6b-45t1, on time-reversal scattering-asymmetry bounds for open resonators, is not cited | Not compared. Priority remains unresolved |

No fatal theorem failure and no proof gap was found.

## Reconciliation with the historical mission (10 October)

`historical-notes/projects/oq7-mission/VERIFICATION_REPORT.md` and `LEAN_STATUS.md` reached the same conclusions: Thm 5.1 fully kernel verified, Thm 7.1 correct but only partially formalized, and no fatal failure. Today's replay independently re-confirms the Lean part on the current checkout. The manuscript's own verification appendix was written without access to that project, which explains G-1.
