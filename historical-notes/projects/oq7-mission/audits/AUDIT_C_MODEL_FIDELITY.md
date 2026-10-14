# Independent Audit C: physical and mathematical model fidelity

Date: 10 October 2026. This is a separate AI-agent review, written before reconciliation with Audit A or Audit B. It is not external human peer review, a Lean proof, or a numerical reproduction. Both manuscripts were read completely, including appendices and references. Notation involving conjugation was additionally checked visually on Paper B pages 6 and 8 and Paper A pages 14 and 20 because plain-text extraction drops some overbars.

## Sources and availability

| Item | Independently inspected local source |
| --- | --- |
| Paper A | `C:\Users\Daniel\Downloads\OQ7_generalized_research_2026-10-10.pdf`; 41 pages; title page: *Reciprocal absorption-scattering asymmetry: sharp channel bounds, exact vector dielectric constructions, and a restricted thickness law*; dated 10 October 2026 |
| Paper B | `C:\Users\Daniel\Downloads\OQ7_compact_Maxwell_cross_sections_2026-10-10.pdf`; 24 pages; title page: *Compact reciprocal Maxwell scatterers can approach unit absorption asymmetry*; dated 10 October 2026 |
| Paper A SHA-256 | `3f01036ff6bc99939b1f2b1a8a205ac4e755188930535db1336d841ca7d377bf` |
| Paper B SHA-256 | `eb85dd064e8dd2410c0b6f88cd6463c2d0700a3b35dcc307cd152cf8f3c4cd6a` |
| Existing physical Lean project | Available separately at this workspace's `outputs/oq7`, with the older scalar physical formalization; its build and statement-equivalence audit belong to the mission's Lean audit |
| Claimed new 43-theorem supplement | Not located in local Downloads, Desktop, Documents/Codex, attachments, synced ChatGPT projects, or either OneDrive root, excluding `.lake`, `.git`, and `node_modules` |
| Claimed numerical/source packages | The two PDF files describe packages, but their existence is not demonstrated by the PDFs alone. No new source package was recovered by this local search |

Paper A page 31 specifies Lean 4.19.0, Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`, 43 authored theorems and 55 kernel theorem constants. Appendix B names six modules: `Algebra`, `Scattering`, `Universal`, `FinitePorts`, `Sharpness`, and `OverlapCertificate`. Those statements are useful retrieval information, not verified local source or build evidence. Paper A's historical statement that the 692-theorem project was unavailable to its author should not be propagated as a statement about this current workspace.

## Verdict within this audit's remit

No fatal physical-model substitution, missing outgoing channel, reciprocity sign error, or illicit order-of-limits interchange was found in Paper B's compact construction. An independent reconstruction supports Theorem 3.1 under its exact fixed strictly absorbing stack hypotheses, and supports its use in Theorem 3.11 and Theorem 1.1. This is an ordinary mathematical assessment, not FULLY KERNEL VERIFIED status.

The longitudinal distributional Green term is essential and is actually present. The aperture-independent bound is an inverse/coercivity bound; the authors do not require the direct Green operator norm to be aperture independent. The grazing singularity is handled in transverse Fourier L1 with local spatial L2, and its square is never integrated. The complete scattered-power convergence follows from two exact energy identities and does retain forward diffraction.

Paper A keeps the scalar physical class, the abstract channel class, the infinite planar body, and the finite-power beam class distinct. Its Theorem 7.1 supplies abstract operator equality witnesses and makes no local Maxwell realization claim for those witnesses. This boundary is scientifically material and must survive any formalization.

## 1. Reconstructing the exact compact Maxwell problem

Paper B assumes a bounded Lipschitz aperture, finite positive thickness, a measurable tensor susceptibility with complex transpose symmetry, operator norm at most K, and Hermitian imaginary part at least delta times the identity, with delta positive. For each finite aperture these are bounded local coefficients supported in a compact prism. The tensor may mix longitudinal and transverse electric components. No magnetic material, surface sheet, or nonlocal constitutive law is introduced.

The time convention is exp(-i omega t). The electric polarization variable is P = chi E, divided by epsilon_0. The electric current would instead be -i omega epsilon_0 P. Confusing these two variables would change the Green factor and the cross-section prefactors; the manuscript does not make that substitution.

Let U = g_k * P for zero-extended P, with (-Delta-k^2)g_k = delta_0. Define

```text
T P = k^2 U + grad div U.
```

Distributional vector identities give

```text
(curl curl - k^2)(k^2 U + grad div U) = k^2 P.
```

Thus E = f + T P satisfies the exact electric Maxwell equation when f is an entire incident vacuum wave. Inside the body, `(chi^-1 - T_R)P = f` gives E = chi^-1 P and therefore P = chi E. Outside, P is zero. Equivalently, `curl curl E - k^2 epsilon E = 0` holds globally in the distributional sense.

For compactly supported L2 P, U is locally H2 by scalar Helmholtz regularity. Therefore E is locally L2, curl E is locally H1, and E is locally H(curl). Set the normalized magnetic field to curl E/(ik). The other curl equation follows from the electric equation. In particular, there is no unaccounted surface current at the vertical aperture faces: the global weak equations encode tangential transmission conditions. Taking a divergence also gives div(epsilon E)=0 distributionally, so bound surface charge is accounted for rather than discarded.

The outgoing fundamental solution gives the scattered field its radiation condition. To close the converse, subtract T(chi E) from any admissible outgoing scattered field. The difference solves the homogeneous whole-space electric Maxwell equation. Its divergence is zero because k is positive, so each component solves the whole-space homogeneous scalar Helmholtz equation. An everywhere regular outgoing Helmholtz solution is zero by whole-space outgoing uniqueness (equivalently, regular spherical waves cannot also be purely outgoing). Thus every finite-energy outgoing weak solution has the same Green representation. This fills in the short converse sentence on Paper B page 8 without an anisotropic-to-isotropic reduction.

This derivation covers the measurable tensor hypothesis directly. The cited Yurkin-Mishchenko 2018 article explicitly describes isotropic materials in its abstract, so citing that paper alone would not establish the stronger tensor statement. The distributional derivation above is what supplies the tensor correspondence here. The cited article does independently confirm the importance of singular kernels, transmission conditions, and locally finite energy: [official publication](https://journals.aps.org/pra/abstract/10.1103/PhysRevA.97.043824).

## 2. Singular Green operator and coercivity

Split the kernel into its Newtonian and outgoing remainder parts:

```text
T = grad div(g_0 * .) + k^2(g_k * .) + grad div((g_k-g_0) * .).
```

The first term has full-space Fourier multiplier `-xi xi^T / |xi|^2`, a bounded orthogonal-projection multiplier with minus sign. It includes the real local distributional contribution. The Hessian of g_k-g_0 behaves as O(1/r) near zero, and k^2 g_k is also locally integrable. On each finite difference domain, Schur's bound makes the remainder a bounded L2 operator. Its constant may grow with aperture. No uniform direct-operator bound is used later.

At real k, the imaginary scalar kernel is smooth, including at the origin:

```text
Im g_k(r) = k/(16 pi^2) integral_S2 exp(ik n.r) dOmega.
```

Applying k^2 I + grad div gives the transverse projector k^2(I-nn^T). Consequently

```text
Im <P,T_R P>
 = k^3/(16 pi^2) integral_S2
     |(I-nn^T) integral_D P(y) exp(-ik n.y)dy|^2 dOmega >= 0.
```

The real local term has zero Hermitian imaginary part. Because finite-domain L2 embeds in L1, Fubini and L2 approximation justify this identity for the stated polarization space; it does not require the polarization to be pointwise smooth.

The loss identity is an exact matrix identity, including for nonnormal tensors:

```text
W = -Im chi^-1 = chi^-dagger (Im chi) chi^-1.
```

Since `|chi^-1 v| >= |v|/K`, it gives `W >= (delta/K^2) I`. Conversely, strict positive imaginary part ensures chi is invertible and `||chi^-1|| <= delta^-1`, so W is a bounded multiplication operator. Therefore

```text
-Im <P, (chi^-1 - T_R)P> >= (delta/K^2)||P||^2.
```

The form i<Q,L_R P> is bounded for each R and has this positive real coercivity. Complex Lax-Milgram yields surjectivity and uniqueness; Cauchy-Schwarz then yields `||L_R^-1|| <= K^2/delta`. This step does not infer surjectivity merely from a lower norm bound. The constant is independent of aperture for a fixed material profile, exactly as needed. It is not uniform if delta tends to zero or K grows.

## 3. Radiation, energy, and time-reversal signs

The far field reconstructed from the same distributional volume operator is

```text
F_P(n) = k^2/(4 pi) (I-nn^T) integral_D P(y) exp(-ik n.y)dy.
```

Multiplying the preceding imaginary-form identity by k gives precisely `integral_S2 |F_P|^2`, with no omitted impedance or polarization factor when incident electric amplitude is one. The full transverse projector includes both radiating polarizations. This is complete scattering, not the power in two specular collection cones.

With the conjugate-linear-first inner product, the volume equation gives

```text
sigma_ext = k Im<f,P>,
sigma_abs = k<P,WP>,
sigma_sca = k Im<P,T_R P>,
sigma_ext = sigma_abs + sigma_sca.
```

The sign follows because `<P,f> = conjugate(<f,P>)`; forgetting that conjugation reverses the energy identity. The overbar is present in the PDF on page 8. Projecting F_P in the forward direction also gives `sigma_ext = (4 pi/k) Im(e^dagger F_P(d))`.

The reversed incident electric wave is `conjugate(e) exp(-ik d.r)`. Its magnetic field is the conjugate magnetic field with an additional minus sign. Paper B equations (1) and (16) have these signs, and Paper A's background antiunitary has the same physical meaning. Opposite propagation with unchanged arbitrary complex polarization would be a different pair.

Transpose symmetry of chi^-1 and distributional Green reciprocity imply symmetry of L_R under the bilinear pairing integral u^T v. Its inverse is bilinearly symmetric as well. For f_- = conjugate(f_+), this gives the same complex forward volume overlap for the pair, hence exact extinction equality. This does not assert that the lossy total solution is the time reverse of the original total solution. Each absorption is strictly positive under the fixed loss floor because its incident right-hand side is nonzero and W is positive definite.

## 4. Longitudinal fiber term and grazing circle

For transverse Fourier wavevector kappa, the outgoing/evanescent branch is beta = sqrt(k^2-|kappa|^2), with nonnegative imaginary part. The scalar Weyl kernel is `i exp(i beta |s|)/(2 beta)`. Its first derivative jumps by -1; therefore

```text
G_kappa'' = -beta^2 G_kappa - delta_0.
```

The transverse-transverse blocks are `(k^2 delta_ab - kappa_a kappa_b)G_kappa*`, the mixed blocks are `i kappa_a G_kappa'*`, and the longitudinal block is `|kappa|^2 G_kappa* - I`. The last -I is required. It is compatible with the familiar three-dimensional local `-I/3` contribution: the transverse transform of the remaining principal-value part also contributes to the resulting longitudinal multiplier. One must not replace the fiber's -I by -I/3.

At normal incidence, the longitudinal component is exactly -q_3. This incorporates D_z=0 and longitudinal-field elimination for a general coupled tensor; it does not assume q_3 is zero. The planar radiation identity involves only transverse q, as Maxwell transversality requires.

Schur bounds on the fixed longitudinal interval give a possible fiber singularity proportional to `||kappa|-k|^-1/2`. In two transverse dimensions, polar measure is rho d rho d theta, so this singularity is locally L1 near the circle. Its square is generically not integrable. At high frequency the quoted upper bound grows at most linearly. Near kappa=0 the outgoing kernels vary smoothly in operator norm.

The outgoing Weyl representation is interpreted as a tempered-distribution identity, not as a globally L2 electric field. The radiation singularity therefore is not removed by assigning an arbitrary value on the light circle. Its locally integrable boundary value is retained in the inverse transform.

## 5. Independent reconstruction of localization

For a fixed smooth compactly supported g inside the aperture, set g_R(x)=g(x/R). Fourier transforming the trial polarization g_R q yields

```text
Hhat_R(kappa) = R^2 ghat(R kappa)(T_kappa-T_0)q.
```

Below |kappa|=k/2, the operator difference is O(|kappa|). Hilbert-valued Plancherel therefore bounds the low-frequency field by `C||q|| ||grad g_R||_2`; in two transverse dimensions the gradient norm is independent of R.

Above k/2, choose N>3. Schwartz decay gives `|ghat_R(kappa)| <= C R^(2-N)|kappa|^-N`. The L1 fiber integral is finite: the light-circle contribution is integrable and the radial large-frequency estimate is rho^(2-N). The inverse Fourier L1-to-Linfinity estimate gives O(R^(2-N)) in the longitudinal Hilbert norm at every transverse point. Restricting to an aperture of area O(R^2) costs only an additional factor R. Thus the high-frequency part is O(R^(3-N)) in local L2. There is no global Plancherel estimate across the light circle.

Approximation of q by smooth longitudinal profiles is legitimate at each fixed R: the restricted three-dimensional T is bounded on the enclosing finite domain, low-frequency convergence is global L2, and high-frequency convergence is local Linfinity with values in the longitudinal L2 space. These identify the inverse-transform limit with the actual outgoing convolution. The window does not modify the coefficient, physical aperture, or incident wave.

The exact trial residual is `(g_R-1)f-H_R`. Uniform coercivity bounds the current error, and comparing the trial with the constant planar current gives

```text
limsup_R ||P_R-q||_(L2(D_R))/R
 <= (c^-1||f||_H+||q||_H)||1-g||_(L2(Omega)).
```

Take the large-aperture limit at fixed g, then approximate 1 by compactly supported smooth g in L2(Omega). This proves o(R). No derivative control on a sequence of sharpening g is tacitly inserted.

The incident, exact current, and planar current norms are O(R). The linear extinction functional and bounded absorption quadratic form therefore differ from their area-scaled planar values by o(R^2). For total scattering, subtract the exact finite and planar energy identities. This proves the complete integrated scattering limit even when the far-field pattern develops a narrowing forward diffraction peak.

A useful normalization check is a perfectly matched opaque planar absorber: planar absorption tends to 1, transmission to zero, and extinction and scattering densities tend to 2 and 1. The scattering limit includes the forward shadow/diffraction contribution. Replacing it by reflected power alone would give zero and would be wrong. Paper B's reference-relative transmission and energy definition give the correct 1.

## 6. Square-aperture rate and dimensions

The interior cutoff differs from 1 on area O(Rw), has gradient L2 norm O(sqrt(R/w)), and fifth-derivative L1 norm O(Rw^-4). Its high-frequency Fourier bound gives a local error O(R^2 w^-4). Thus, with separate fixed-stack constants, the current error is bounded by a sum proportional to

```text
sqrt(Rw) + sqrt(R/w) + R^2 w^-4.
```

Writing dimensionless lengths rho=kR and omega=kw avoids mixing the dimensions carried by those constants. Choose omega=rho^(1/3). The three dimensionless orders are rho^(2/3), rho^(1/3), and rho^(2/3). Restoring the fixed length unit multiplies the current norm by its appropriate dimensionful factor. Dividing the linear/quadratic cross-section errors by R^2 gives O((kR)^(-1/3)). The constant may depend on kL, K, delta, the polarization, and the positive planar extinction when one subsequently divides by that extinction. The estimate supplies no uniform cost law along the final construction sequence.

No dimensionally inconsistent variable frequency limit is taken. The prose around Paper B equation (61) would be clearer with separate dimensionful constants or scaled coordinates, but the fixed-k assertion and equation (62) already specify the needed reference length. This is an expository improvement, not a failed rate estimate.

## 7. Actual planar coefficients, regularization, and compact supremum

The first layer is diag(1+i eta,1,1). One linear polarization sees exact vacuum, while the orthogonal polarization has the ordinary lossy scalar slab response. Its absorptance is strictly between zero and one: positive loss excludes zero, and nonzero finite transmission excludes one.

For any fixed P>1, choose j so that `[2j/(2j-1)]^2 <= P`. The plate's real transverse eigenvalues are 1 and that squared index, and its thickness is `(2j-1)pi/k`. Its two optical phases are odd pi and even pi. Matching tangential E and H therefore gives exact zero reflection and Jones transmission -V; after dividing by vacuum propagation it is V. These are finite local tensors, not ideal transformers. The longitudinal eigenvalue is 1 and the transverse-longitudinal couplings are zero.

For opposite real y-polarized incidence, one direction is lossless and the other deposits `(1-t^2)A_x`. Both have reference-relative co-polar transmission t and common extinction `2(1-t)`. This includes polarization-converted outgoing power. As eta=1/m, kh=m^2, and t=1-1/m, the slab reflection vanishes, transmission decays, A_x tends to one, and the normalized absorption difference tends to one.

The construction with semidefinite loss is not substituted directly into the strictly absorbing localization theorem. For one fixed finite member, add i delta I to both layers. Finite-dimensional Maxwell propagation and passive boundary matching give continuity at delta=0 even though chi^-1 itself can be singular there. The outgoing homogeneous planar problem has zero exterior amplitudes by flux balance and hence zero internal field by ODE uniqueness; thus the matching system is invertible at the unregularized member.

After choosing that fixed member, choose a fixed sufficiently small positive delta. The real cap is unchanged and the loss eigenvalues are at most eta+delta or delta. Taking eta<Q/2 and delta<Q/2 respects every fixed Q>0. Only then enlarge the aperture at fixed thickness and positive loss floor. The positive limiting extinction density permits division and ratio convergence. Repeating these finite choices is a diagonal existence construction, not an interchange of aperture and lossless limits.

For each individual regular compact object, equality at positive extinction would require zero scattered power in the more-absorbing experiment. The continuous volume far field would then vanish on the entire sphere, including forward, contradicting the forward optical theorem. Nonattainment is sound. Large apertures evade fixed-directivity bounds; no common diameter, volume, thickness, loss floor, integrated loss, or bandwidth is imposed by the supremum theorem.

The single-frequency material values also have a passive causal interpretation: the real symmetric constructed tensors have fixed real principal axes, and each target eigenvalue 1+a+ib with a>=0, b>0 is realized at the working frequency by a positive-strength damped Lorentz oscillator. Its oscillator energy balance establishes passivity. This does not assert the same caps or performance over a nonzero bandwidth.

## 8. Dipolar model and numerical model boundaries

Independent sphere integration of the dipole far field gives

```text
integral_S2 |(I-nn^T)p - n cross m|^2 dOmega
 = (8 pi/3)(|p|^2+|m|^2).
```

The electric-magnetic cross term integrates to zero by oddness in n; it remains in the angular pattern. With the paper's factor 3/(2k), this gives `6 pi/k^2 ||Af||^2`. Its forward projection gives the stated extinction with the same sign. The magnetic minus-transpose reciprocity law, the J change of basis, and `I-S^dagger S=4 J^dagger Q_A J` are consistent. The plane-wave pair is orthogonal in those dipole coordinates, but it is not being treated as a unit finite-power state in the infinite Maxwell channel space.

The dipolar equality tensors are radiation-consistent point-response models. They do not establish a local dielectric completion, and Paper B expressly separates that gap from its independent aperture proof. The dipole statement that contrast tending to one forces extinction tending to zero is not transferred to arbitrary large compact objects.

The reported DDA uses point polarizations with an exact full-sphere radiation Gram matrix, not only specular channels. That is a physically appropriate discrete model. At finite spacing it remains a discrete model, with cell-response and continuum-discretization errors. Optical-theorem closure of a solved discrete system cannot certify continuum convergence. The reported solver-limit runs and mesh sensitivity are openly retained. Missing source archives prevent this audit from independently reproducing those numerical claims; none is used in the reconstruction above.

## 9. Paper A physical scope and correspondence

| Result | Model-fidelity finding | Status supported by this review |
| --- | --- | --- |
| Lemmas 4.1-4.4 and Theorem 4.5 | Scalar finite layers, actual scattering-field Gram identity, nonzero transmission, finite-interface comparison, capped density, singular-inclusive PSD aggregation, and uniform changing-stack quantifier are preserved. The selected interval may have passive surroundings; padding by zero-loss vacuum respects a thickness cap | Ordinary physical proof survives this model review; formal equivalence belongs to the separate Lean audit |
| Theorem 5.1 | Exact M,T,a, all widths, continuously selectable material coefficients, no minimum feature size, strict active branch, positive k/P/Q/M conditions, and all real large budgets are explicit. Negative exponents occur only in algebraic factorization; physical spacers are positive eventually. Matching coatings use ordinary bounded indices and add O(1/k) thickness | No model substitution found; full physical formalization must match these exact quantifiers |
| Theorem 6.2 | Complete power-normalized channel operator with a specified unitary reciprocal background. Extinction is reference-relative, not total output power. Opposite inputs are related by the background antiunitary | Abstract channel theorem; no compact plane-wave area normalization inferred |
| Theorem 6.3 | Scalar two-port contrast uses vacuum-normalized transmission, including its phase. A vacuum spacer cannot adjust that phase; the supplied reflectionless dielectric phase slab can | No physical reference-phase error found |
| Theorem 6.4 | Actual four-port planar Maxwell construction with two polarizations on each side. Positive semidefinite tensor loss allows a loss-free incident field; positive total tensor loss does not imply a scalar two-input Gram floor | Ordinary physical construction; laterally infinite support |
| Corollary 6.5 | Finite-power angular spectra, smooth power bases near normal incidence, correct conjugation and transverse-wavevector reversal, and exact extinction retuning. The material body remains infinite laterally | Finite incident power does not establish compact material |
| Theorem 7.1 | Complete operator compression preserves contraction budgets and forward overlap. Equality witnesses establish the abstract maximum but are not asserted to be local Maxwell scatterers | Abstract ordinary theorem; the generic PSD certificate alone is not the full formal statement |

Paper A's initial Poincare/Taylor presentation of the scalar comparison is supplemented by the first-zero argument in Appendix A; the latter avoids dividing by the initial field zero. The separate half-period convexity and full-period supporting tangent prevent an invalid full-period Jensen step. The direct product remainder and all-eight-real-entry matching map in the appendix preserve the actual physical construction. Nothing in that appendix changes the scalar model into a generic response assumption.

The abstract Theorem 7.1 upper compression and finite-channel equality witnesses do not supply locality, material caps, a boundary-value problem, or a realization of those witnesses. Paper A states this limitation clearly. A future Lean theorem for the channel problem must retain that label and must not be cited as a physical Maxwell equality theorem.

## 10. Issues and remaining certification obligations

| Finding | Classification | Required treatment |
| --- | --- | --- |
| The cited 2018 VIE paper's advertised isotropic scope is narrower than B's measurable tensor statement | Expository/citation scope issue, with a rigorous direct repair given in Section 1 above | State the weak distributional derivation and the whole-space outgoing uniqueness argument explicitly; do not rely on an isotropic reference alone |
| Whole-space outgoing uniqueness is compressed into one converse sentence in B | Expository issue; no counterexample found | Include the homogeneous-difference argument, divergence reduction, and regular outgoing Helmholtz uniqueness lemma in the final analytical account and future formalization |
| Current-norm dimensions are hidden in the combined fixed-stack constant in B equation (61) | Expository issue, not a rate failure | Use dimensionless lengths or separate constants when reporting the quantitative rate |
| New 43-theorem supplement and numerical/source archives not found locally | Source availability limitation | Obtain actual sources and run the audits before crediting their reported compilation or numerical reproduction |
| Paper A's unavailable-692-project prose is historical and does not describe this workspace | Verification-status correspondence issue | Record the recovered project's actual declarations and hashes separately, then verify equivalence to Paper A's scalar theorem |
| Maxwell operator infrastructure and localization not Lean formalized by these papers | Unfinished formal certification | Prove the actual distributional operators, outgoing correspondence, optical identity, Weyl estimates, and localization; a conditional squeeze lemma cannot replace them |

This audit found no fatal theorem failure or essential unstated physical assumption in the compact supremum construction. The exact strict-loss, fixed-stack hypothesis is essential to the stated proof, and the manuscript already retains it. Lossless or uniformly resource-bounded variants would require new arguments. Novelty has not been assessed by this audit and cannot be inferred from this mathematical assessment.

