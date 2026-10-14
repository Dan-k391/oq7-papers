# Quartic Maxwell paper: mathematical audit

Date: 14 October 2026. Auditor: AI-assisted (Claude), commissioned by Daniel Wang. This is not human peer review.

**Audited version:** `papers/quartic-maxwell/manuscript/OQ7_quartic_Maxwell_2026-10-10.pdf`, 17 pages, SHA-256 `576478ba88fd374e724b96e07c5e3e1648485cd163dc4d8ba9cd0b3ef52eac62`.

The equations were read from the PDF. Layout-mode extraction was used where plain extraction is ambiguous; see the workflow note on column-order hazards. The reconstructed `arxiv/main.tex` revision served only as a reading aid. It is not the audited object.

The audit followed the main paper's three-strand process. Each strand was worked out from definitions before the earlier quartic audit (`audits/OQ7_quartic_adversarial_audit_2026-10-10.pdf`) was consulted. The reconciliation with that audit is at the end.

## Claim register and dependencies

| Claim | Depends on | Verdict |
|---|---|---|
| Thm 1.1, uniform bound Γ ≤ min{1, (2/3π)ρ²L_k k⁴RV} and (6) | Lemmas 3.1–3.4, eqs. (22)–(24) | Correct. Needs χ ∈ L^∞ (measurable), see Q-1 |
| Lemma 3.1, ‖K₀‖ ≤ 1 and ‖K_k−K₀‖ ≤ (3/4)k²a_v² | dyadic eigenvalues (15), rearrangement, Schur test | Correct |
| Lemma 3.2, radiation identity (17), ‖F_k‖² ≤ 8πV/3, cross sections (19) | Funk–Hecke-type plane-wave identity for sin(kr)/(4πr) | Correct |
| Lemma 3.3, coercivity W ⪰ ρ⁻¹, ‖T_k‖ ≤ ρ, weak Maxwell equivalence | loss floor, Lax–Milgram, H²_loc regularity, vacuum uniqueness | Correct |
| Lemma 3.4, reciprocal extinction and X > 0 | bilinear symmetry of T_k, f₋ = conj f₊ for real e | Correct |
| Thm 4.1, Γ = (2/(3πD₀))\|Im p₀†p₁\| t⁴ + O(t⁶) for a fixed rescaled pattern | (27)–(32) | Correct |
| Thm 1.2, two-sphere coefficient interval and remainder 21t⁶/2000 | Thm 4.1, §5.1–5.4 | Correct. All constants re-derived and kernel-checked |
| Thm 1.3, sup Γ = Θ_{m,M}((kR)⁴) | Thm 1.1, Thm 4.1, §6 | Correct. Lower constants re-derived and kernel-checked |
| §5.5, passive Lorentz realizations | elementary | Correct |
| §7, Table 1 numerics | unrecovered solver | Independently corroborated (route 2 below); not a proof |

## Audit A: analytic re-derivation

**Theorem 1.1.**
- *Lemma 3.1.* The radial eigenvalue −2b(u)/(4πr³) and the tangential eigenvalue (u²e^{iu}+b(u))/(4πr³), with b(u) = e^{iu}(iu−1)+1, were rederived from (k²+∇∇)e^{ikr}/(4πr). The contact terms −δI/3 are identical in the static and dynamic kernels and cancel. b′ = −ue^{iu} gives \|b\| ≤ u²/2, so the kernel norm is at most 3k²/(8πr). The rearrangement bound sup_x∫_D dy/\|x−y\| ≤ 2πa_v² and Schur's test then give exactly (3/4)k²a_v².
- *Lemma 3.2.* Im g_k = (k/16π²)∫e^{ikn·x}dΩ, and applying (k²+∇∇) inserts k²Π_n, which gives (17). Cauchy–Schwarz and ∫Π_n dΩ = (8π/3)I give (18).
- *Cross sections.* A = k⟨p, Wp⟩ follows because −Im_H χ⁻¹ = χ^{-†}Bχ⁻¹ = χ⁻¹Bχ^{-†}; both factorizations were checked. Taking the imaginary part of ⟨p, Lp⟩ = ⟨p, f⟩ gives X = A + S with S = (k⁴/16π²)‖Fp‖², consistent with the far-field amplitude k²Fp/(4π).
- *Lemma 3.3.* \|v†χv\| ≥ v†Bv ≥ m\|v\|² gives ‖χ⁻¹‖ ≤ 1/m, and then W ⪰ m/M². E = f + (k²+∇∇·)(g_k∗p) solves curl curl E − k²E = k²χE distributionally. The converse holds by entire outgoing vacuum uniqueness. No boundary regularity is used.
- *Chain (22)–(24).* ‖f₊−f₋‖² = ∫4sin²(kd·x) ≤ 4k²R²V; ‖p±‖² ≤ ρX/k; √V ≤ L_k h. The difference of the quadratic radiation forms then gives \|S₊−S₋\| ≤ (k⁴V/6π)‖Δp‖(‖p₊‖+‖p₋‖) ≤ (2/3π)ρ²L_k k⁴RVX. With V ≤ 4πR³/3 and a_v ≤ R this gives the coefficient 8/9 in (6). The final algebra is kernel-checked (`OQ7Quartic.quartic_chain`), with the analytic estimates as explicit hypotheses.

**Theorem 4.1.**
- ‖T_t−T₀‖ = ‖T_t(K_t−K₀)T₀‖ = O(t²), with no O(t) term.
- The decomposition f± = c_t ± i s_t gives (S₊−S₋)/(k⁴R⁶) = −4 Im⟨u_t, Q_t v_t⟩. Because v_t = O(t), every correction is t·O(t²), and the next term in the expansion is O(t³).
- Bilinear symmetry cancels the mixed forward terms, so X/(kR³) = D₀ + O(t²) and D₀ = ⟨q₀, Wq₀⟩ > 0. Dividing gives (26).
- Origin shifts change p₁ by a real multiple of p₀, so Im p₀†p₁ is translation invariant.

**Theorem 1.2.**
- Identity (38), ∫T_j h = β_j∫h, follows exactly from bilinear symmetry.
- β₁ = 3(1+3i)/10, β₂ = 6(2+3i)/13, and α_j, I_b = −(8/195)w², D_b = (173/130)w were recomputed in exact rational arithmetic.
- The interaction constants were recomputed: c = 4√2/14739 < 1/2500, δ < 1/600, the relative error 1404585/14400000 < 1/10, and the interval 2304a³/10393 ≤ C ≤ 2816a³/10367.
- The full-Maxwell remainder constants were recomputed: 81/25, 9/5, the radiation terms 54/125, 81/125 and 3/5, the extinction constant 108/25, the division constant 55656/8125 < 7, the remainder 21/2000 and the lower bound 27/1299125.
- All of these are exact or kernel-checked (`checks/certificates.py`, `lean/QuarticCertificates.lean`).

**Theorem 1.3.**
- The mean-value identity (56) holds for the harmonic static kernel.
- The first interaction p₀⁽¹⁾ = 2g₀β²v₁v₂e_x is exact, and the centre terms of p₁⁽¹⁾ cancel because z₁+z₂ = 0.
- ‖DH‖ ≤ 6/(π\|r\|⁴).
- The constants were checked: L = 2688π²μ³a⁹/(9+μ²)², the coefficients 48√3/7, 54/35 and the choice (65) giving ≤ 1/2, the bounds μw/(1+μ)² ≤ D₀ ≤ μw, and 224/3 ≤ C_h/(μ²a⁶/(9+μ²)²) ≤ 224(1+μ)².

## Audit B: counterexamples and edge cases

- **Measurability (Q-1).** The caps in (1) do not make χ a multiplication operator. Both proofs need χ ∈ L^∞(D; C³ˣ³). A non-measurable pointwise-admissible χ makes the cross sections undefined. This is a statement gap, not a counterexample to the bound.
- **Degenerate resources.** The constants blow up as m → 0 or M → ∞, as the paper states. Bounded negative real contrast is allowed and the proof never uses Re χ. A loss floor on only part of D is outside the theorem.
- **Polarization.** For elliptical e, f₋ ≠ conj f₊ with the same constant vector, so (22) has no small factor. The theorem correctly excludes this case.
- **Tightness.** For the two-sphere example (m = 1, M = 2) the bound (6) is ≈ 28t⁴, against the attained ≈ 3.08×10⁻⁵t⁴. This is valid but very loose. The paper claims only the exponent, not the prefactor.
- **Range and extinction.** The remainder (8) is proved only for t ≤ 1/4, and the lower bound only for t ≤ 1/40, both as stated. Extinction vanishes in the Theorem 1.3 family; there is no fixed-extinction claim.
- **Independent numerical cross-checks.** These are diagnostics, not proofs; see `checks/two_sphere_crosscheck.py` and `checks/results/`.
  1. *Static single exchange.* This is an exact one-exchange computation of p₀ and p₁, including the induced quadrupolar response 5χ/(5+2χ) derived here. It gives C ≈ 3.0772585×10⁻⁵. The manuscript's numerical extrapolation is 3.0772563×10⁻⁵, a relative gap of 7×10⁻⁷, which is the size expected from the neglected multiple exchanges. Both lie inside the proved interval [2.771, 3.395]×10⁻⁵.
  2. *Dynamic coupled electric dipoles with exact Mie a₁.* This route reproduces Table 1 at every t, to relative differences of 1×10⁻⁵ (t = 0.025) through 3.6×10⁻⁴ (t = 0.4). Extinction reciprocity holds to rounding. The model omits magnetic and quadrupole moments, so this route checks only normalization and magnitude.

## Audit C: model fidelity

- The cross sections are those of unit-amplitude vacuum plane waves, with scattering over the full sphere and both polarizations. The forward optical theorem is consistent with (19).
- Both experiments use the same local χ and the same inverse T_k; the time-reversed pair is correct for real e. No dipole approximation enters any proof.
- The passive Lorentz laws (52) realize χ_j = ij at ω₀ with poles in the lower half-plane. The result is a fixed-frequency size limit, as stated.

## Classified issues

| ID | Class (main-paper vocabulary) | Issue | Effect |
|---|---|---|---|
| Q-1 | Missing or unjustified assumption | χ must be essentially bounded and measurable (χ ∈ L^∞) | Statement repair only. Already flagged in the 10 October audit and fixed in the reconstructed revision |
| Q-2 | Reproducibility gap | §7 says the solver is "included in the source archive"; it was not recovered | Table 1 now independently corroborated (route 2). The numerical claims remain diagnostics |
| Q-3 | Scope (not an error) | No optimal prefactor and no fixed-extinction sharpness | Stated by the paper. Remains open |

No fatal theorem failure and no proof gap was found.

## Reconciliation with the 10 October adversarial audit

That audit also found only the measurability gap, and also reproduced the sphere certificates and remainder. It additionally notes close prior art: Ammari–Deng–Millien imply quartic upper order for a fixed smooth shape, and Hopkins et al. give the two-dipole mechanism. I did not re-examine those sources. Its priority conclusion stands: priority for the uniform theorem is unresolved.
