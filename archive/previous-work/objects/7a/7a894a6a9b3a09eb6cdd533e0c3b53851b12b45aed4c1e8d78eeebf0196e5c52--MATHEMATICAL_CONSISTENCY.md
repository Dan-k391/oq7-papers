# Mathematical consistency of the professor-review corrections

Review date: 2026-10-12. This is an AI-assisted mathematical source review of the authorized correction pass, not independent human certification or a new Lean kernel replay.

**Verdict:** The corrections for P2-01 and P2-05 are mathematically consistent. The main prescribed-extinction theorem and the normalized aperture theorem are preserved. No new theorem, hypothesis, numerical result, or stronger formal-verification claim was introduced by these corrections. The construction caption and vector-drawing specification agree with the Maxwell model.

Reviewed final source: [main.tex](main.tex), SHA-256 `f16221a3ca71708cbc32a08a6bacee2e6b453a394d5282168a3c6e867d9766d3`. Locations below refer to this revision. The pre-correction manuscript was the version identified in [PUBLICATION_ISSUES.md](PUBLICATION_ISSUES.md), SHA-256 `1e2e948ae3cf7fda9399439f0a267e4d7e5605dda5f776354642db7ea18c5ad3`. Reviewed final PDF: [paper.pdf](paper.pdf), 16 pages, SHA-256 `25707ace339ac54cc4dfdb9f2f7711cf3ba6b2ca55193afd77c5b18169551647`.

## Preservation checks

The complete pre-correction LaTeX was retained in session memory and compared with the corrected source.

| Item | Corrected source location | Result |
|---|---|---|
| Theorem 4.1, including material caps, every positive prescribed extinction, exact target, strict per-object bound, and both suprema | main.tex:108-119 | The theorem block is textually unchanged. |
| Theorem 7.1, including angle-uniform normalized current and power limits at fixed positive active losses | main.tex:284-296 | The theorem block is textually unchanged. |
| Numbered mathematical equations | 51 equation environments | All equation bodies are unchanged except the intended replacement of `hat(H)` by `hat(H-tilde)` in Eq. (35). |
| Both exact-extinction arguments and positive-loss regularization | main.tex:357-398, Section 8 | The complete section is textually unchanged. |
| Entire outgoing weak vacuum uniqueness | main.tex:446-467, Appendix A | The complete appendix is textually unchanged. |
| Planar amplitude vectors | main.tex:471-482, Eqs. (50)-(51) | Both displayed vectors are unchanged. Their reference-plane conventions are now explicit. |

The core quantifiers remain fixed wavenumber `k>0`, arbitrary fixed caps `P>1`, `Q>0`, every target `E_*>0`, and every accuracy `0<epsilon<1`. Every witness remains a finite square-aperture two-layer reciprocal, local, anisotropic, nonmagnetic body with strictly positive tensor loss. Resources remain unrestricted across the approximating sequence. No common loss floor or bandwidth guarantee has been added.

## P2-01: global Fourier field and restricted residual

At main.tex:327-343, the revision distinguishes the unrestricted observation field on `R^2 x (0,L)` from its restriction to the material aperture. The source current is still compactly supported and zero-extended in all three coordinates. The layer-axis multiplier is extended only in the transverse observation coordinates.

Write `K_global p = (k^2 I + grad div)(g_k * zeroextend(p))`. With the manuscript notation,

\[
\widetilde H_{R,\theta}
=J_\theta^*\mathcal K\bigl(J_\theta(v_Rr)\bigr)
-v_RB_{\mathbf0,\theta}r,
\qquad
H_{R,\theta}=\widetilde H_{R,\theta}|_{D_R}.
\]

Since `J_theta` depends on height alone, it commutes with the transverse Fourier transform. Also `hat(v_R)(kappa)=R^2 hat(v)(R kappa)`. The distributional Weyl formula therefore gives exactly

\[
\widehat{\widetilde H}_{R,\theta}(\boldsymbol\kappa)
=R^2\widehat v(R\boldsymbol\kappa)
 (B_{\boldsymbol\kappa,\theta}-B_{\mathbf0,\theta})r.
\]

The transform is taken before aperture restriction, as the corrected text states. Transforming the zero extension of the restricted field instead would introduce convolution with the aperture-window transform. That was the original domain ambiguity; it is now resolved.

On the low-frequency disk `|kappa|<=k/2`, the operator-difference bound and Hilbert-valued Plancherel give

\[
\|\widetilde H^{\mathrm{low}}_{R,\theta}\|_{L^2(\mathbb R^2;\mathcal H)}
\le C\|r\|_{\mathcal H}\|\nabla v_R\|_{L^2(\mathbb R^2)}
=C\|r\|_{\mathcal H}\|\nabla v\|_{L^2(\mathbb R^2)}.
\]

The last equality uses the two-dimensional transverse scaling. For the complementary region and an integer `N>3`, Schwartz decay and the stated fiber bound imply

\[
\|\widetilde H^{\mathrm{high}}_{R,\theta}\|_{L^\infty(\mathbb R^2;\mathcal H)}
\le C_{v,N}R^{2-N}\|r\|_{\mathcal H},
\qquad
\|\widetilde H^{\mathrm{high}}_{R,\theta}\|_{L^2(D_R)}
\le C_{v,N}R^{3-N}\|r\|_{\mathcal H}.
\]

The transverse area is `R^2`, giving the extra factor `R` upon restriction. At the grazing circle the inverse-square-root singularity is locally integrable. At infinity the radial integrand is `O(rho^(2-N))`, which is integrable for `N>3`. These estimates are uniform in angle because each layer-axis multiplier has norm one. They do not claim a global `L^2` bound for the whole field across the grazing circle, nor a bound uniform in vanishing active loss or growing layer thickness.

The low-frequency map is bounded into global `L^2`; the high-frequency map is bounded into transverse `L^infinity(H)`. Thus height-profile density extends the identity distributionally and the estimates on the finite observation aperture. Boundedness of the restricted volume operator identifies that local limit with the physical volume field.

The restricted field is the same residual as before. For the planar solution `r_infinity`,

\[
L_{R,\theta}(v_Rr_\infty)-g
=(v_R-1)g-H_{R,\theta}.
\]

Consequently the coercive inverse estimate, fixed-window/aperture/density order, normalized current convergence, power convergence by the work and absorption forms, and scattering convergence by energy balance all survive unchanged. Positive continuous planar extinction still gives a positive lower bound on the compact angle interval. Both prescribed-extinction intermediate-value arguments retain their original hypotheses and margins.

## P2-05: boundary-plane phase conventions

The corrected definitions at main.tex:241, 267, and 470 use electric amplitudes referenced to the adjacent interfaces. A vacuum layer of width `ell` has transmission `exp(ik ell)`, without removal of that propagation phase. Thus the whole-stack vacuum transmitted factor is `v_A v_W = exp(ik(h+d))`.

At the left reference plane `z=0`, the original plus incident field already has unit amplitude. At the right reference plane `z=L=h+d`, unit minus incident amplitude corresponds to `exp(ikL) f_minus = e_y exp(-ik(z-L))`. The overall phase has modulus one. Multiplying both incident and response fields by it preserves extinction, absorption, and scattering. For this right-plane convention, the vacuum transmitted amplitude at the opposite plane is also `exp(ikL)`, not its conjugate.

An independent two-channel cascade uses

\[
R_A=\operatorname{diag}(r_A,0),\quad
T_A=\operatorname{diag}(t_A,v_A),\quad
R_W=r_Wuu^T,\quad
T_W=v_WI+\Delta uu^T.
\]

For plus incidence, the right-going amplitude at the shared interface solves `(I-R_A R_W)a=T_A e_y`. For minus incidence, the left-going amplitude there solves `(I-R_W R_A)b=T_W e_y`. These two systems reproduce all four entries of Eqs. (50)-(51), with denominator `D=1-r_A r_W cos^2(theta)` and the stated ordering of outgoing boundary-plane channels.

In either direction, the co-polar transmitted boundary amplitude is `v_A(v_W+Delta sin^2(theta)/D)`. Dividing by `v_A v_W` gives Eq. (28). The explicit definition at main.tex:267 now agrees with this calculation.

Two checks make the vacuum subtraction unambiguous:

- Vacuum coefficients `r_A=r_W=0`, `t_A=v_A`, `t_W=v_W` give `Delta=0`, both scattered vectors zero, and `t_co=1`.
- The lossless designed plate has `r_W=0`, `t_W=1`, `v_W=-1`. The vectors give `C_plus=4` and `C_minus=4[sin^2(theta)+cos^2(theta)(|r_A|^2+|t_A|^2)]`; together with `Y=4`, these recover Lemma 6.1. The auxiliary zero-angle limit is unchanged.

The earlier 36-case numerical cascade diagnostic supported this algebra to `1.19e-13` in normalized amplitude. It is a floating-point consistency check, not a continuum accuracy certificate or substitute for the derivation.

## Construction schematic

The caption at main.tex:188 and the vector specification in [review/make_geometry.py](review/make_geometry.py), as reflected in [figures/two-layer-geometry.svg](figures/two-layer-geometry.svg), are consistent with the body definition:

- The absorber lies at `0<z<h`, below the plate at `h<z<h+d`.
- Positive `e_z` points upward in the schematic; plus incidence enters from the absorber side and minus incidence from the plate side.
- Both incident electric polarizations are `e_y`.
- The transverse active plate axis rotates from `e_x` toward `e_y`, matching `u_theta=cos(theta)e_x+sin(theta)e_y`.
- The square transverse aperture has side `R`; the displayed section is explicitly not to scale.
- The caption distinguishes intermediate rank-one tensors from the final tensors obtained by adding `i nu I`.

This checks scientific labels and orientation. The final drawing uses the plain label "Incident polarization: e_y" in both vector formats; it has the same scientific meaning and avoids the unsupported parallel-symbol glyph. The post-build presentation check is recorded below.

## Final rendering review

All 16 corrected PDF page views and 22 desktop/mobile HTML screenshots were visually inspected: 11 locations at each of 1440 and 390 pixels, including the main theorem, aperture theorem, schematic, power factorization, Weyl blocks, corrected commutator, electric inverse, Appendix B vectors, formal-verification section, title, and references. The affected views were rechecked after the final formatting adjustments.

The PDF schematic on page 6 is legible and agrees with its caption. Equations (35)-(38) on page 9 visibly retain the corrected global Fourier field and the restricted estimates, with no missing accent, term, or equation label. The planar phase convention is clear on page 7 and pages 13-14. Section 10 on page 12 continues to qualify the frozen manifest and earlier audit evidence; it does not introduce an unsupported final-commit independent-PASS claim.

The visual pass identified an HTML omission caused by conversion of the LaTeX `path` command: the formal-source filename was initially absent. Replacing that command with `texttt` restored the complete filename, which is now visible in both desktop and mobile screenshots. On narrow screens the vector figure remains a compact overview, and the added "Open full-size schematic" link provides access to its readable labels. Long equations retain local horizontal scrolling with visible instructions; no page-wide overflow or inaccessible missing term was found in the inspected views.

Independent read-only structural checks of the final files found 81 internal HTML anchor links with no missing target or duplicate ID; all 51 numbered equations match the LaTeX auxiliary labels. The HTML contains the restored source filename and its full-size SVG link, whose local target exists. The final source and PDF fingerprints above were independently recomputed. The final source comparison again found Theorems 4.1 and 7.1 unchanged, with only Eq. (35)'s intended global-field accent changed among the 51 equation bodies.

No further mathematical, glyph, equation-number, or unrecoverable layout defect was identified. This review used static rendered images and source inspection; it is not a live touch/keyboard accessibility certification or a website-availability check. Authorship and other factual declarations remain pending human approval, and good rendering does not by itself establish publication readiness.

## Formal scope and remaining responsibility

The existing correspondence CSV distinguishes direct Lean statements from ordinary mathematical exposition. Its Weyl-fiber and Appendix B rows do not claim that the corrected Fourier identity or displayed amplitude vectors are individually exported Lean declarations. The principal frozen declaration remains `OQ7Prescribed.theorem11_complete : PhysicalTheorem11Statement` at commit `686402a6c2d63820828729cc7ab02504632e3fe7`.

This reviewer read the principal declaration and the Maxwell-model definitions but did not rerun the complete kernel build or modify the frozen repository. The corrections do not supply the unavailable later independent all-PASS audit, prove first priority, establish experimental realism, or complete the pending human authorship/disclosure decisions. The manuscript remains a draft for professor review until those separate responsibilities are resolved.
