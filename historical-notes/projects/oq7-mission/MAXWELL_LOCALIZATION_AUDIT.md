# Exact Maxwell localization: independent reconstruction

**Verdict:** Paper B, Theorem 3.1 survives the three ordinary mathematical audits under its stated, fixed, strictly absorbing hypotheses. The reconstruction below accounts for the functional-analytic bridges. It does not constitute a complete Lean formalization. The corresponding manuscript result is **ORDINARY PROOF ONLY**; selected generic estimates being formalized are separately marked components.

Sources: preserved Paper B, pp. 6-12; direct reconstruction in `audits/AUDIT_A_ANALYTICAL.md`; separately completed `AUDIT_B_COUNTEREXAMPLES.md` and `AUDIT_C_MODEL_FIDELITY.md`. Both source PDFs and their hashes are in `reference_manifest.json`. Conjugation and longitudinal local terms were checked against rendered pages, rather than solely extracted text.

## 1. Exact hypotheses and observable definitions

Fix k>0, L>0, a bounded open Lipschitz Ω⊂R² of positive area, and a measurable 3×3 complex susceptibility χ(z), z∈(0,L), with χᵀ=χ, `Im_H χ≥δI` for a fixed δ>0, and `||χ||≤K<∞`, all for almost every z∈(0,L). The boundedness is an essential bound. Both χ and all these constants are fixed as R grows. Set `D_R=RΩ×(0,L)`, ε=I+χ in D_R and ε=I outside, µ=I. No smoothing of this physical aperture is performed. Trial windows below only approximate currents.

Take a transverse unit complex polarization e and incident electric fields `f₊=e exp(ikz)`, `f₋=bar(e) exp(-ikz)`. Their magnetic fields have the additional time-reversal sign. The source convention is exp(-iωt). Cross sections divide powers by the unit-amplitude incident intensity. The target planar solution has polarization current q(z), extended as constant in the transverse coordinates. Its planar power densities per transverse area are X∞, A∞, C∞.

The theorem claims, separately for these two inputs,

`σ_ext,R/(R²|Ω|)→X∞`, `σ_abs,R/(R²|Ω|)→A∞`, `σ_sca,R/(R²|Ω|)→C∞`.

The scattering cross section integrates every outgoing solid angle and both polarizations. The claim is not a uniform estimate over changing stacks or a finite-power incident-beam theorem.

## 2. Green operator, distributional singularity, boundedness

Let `g_k(x)=exp(ik|x|)/(4π|x|)` and `T P=(k²I+∇div)(g_k*P)` for a compactly supported L² vector field P. Restrict its zero-extended action to D_R to obtain T_R.

Write `T=∇div(g_0*) + [k²g_k I+∇div((g_k-g_0)*)]`. On full-space L² the first term is the bounded Fourier multiplier `-ξξᵀ/|ξ|²` (value at ξ=0 immaterial). Its distributional Hessian contains a delta term; replacing it by an unregularized pointwise r⁻³ kernel would be incorrect. For the second term, `g_k-g_0=ik/(4π)+O(r)` and its second derivatives are O(r⁻¹). The k²g_k term is also O(r⁻¹). These are locally integrable in three dimensions. On the finite bounded set D_R-D_R their absolute kernel integrals are finite, so Schur's test gives L²(D_R) boundedness. This is sufficient for each R. Its constant may grow with R.

For compact L² P, `P∈L¹` by Cauchy-Schwarz and bounded volume. The exact distribution identity

`Im g_k(x-y)=k/(16π²) ∫_{S²} exp(ik n·(x-y)) dΩ(n)`

is smooth, including at x=y. Differentiation gives the transverse projector I-nnᵀ and hence

`Im⟨P,T_RP⟩ = k³/(16π²) ∫_{S²}|(I-nnᵀ)∫_{D_R}P(y)exp(-ikn·y)dy|² dΩ ≥0`.

All integrals here are justified by compact L¹ support and the bounded sphere integrand. The far field is

`F_P(n)=k²/(4π)(I-nnᵀ)∫P(y)exp(-ikn·y)dy`.

It is continuous on the sphere. Expansion of g_k at large radius is uniform in n for fixed compact support; differentiating the expansion supplies the electric far field. Finite first moments of P are enough for the remainder, and compact L² support supplies them. Therefore `∫|F_P|²=k Im⟨P,T_RP⟩`. No angular channel is discarded.

## 3. Volume-integral equation and an aperture-independent inverse

Strict loss makes χ invertible almost everywhere, with `||χ⁻¹||≤δ⁻¹`: apply `δ||v||²≤Im(v†χv)≤||v||||χv||`. Set

`W=-Im_H χ⁻¹=χ⁻†(Im_Hχ)χ⁻¹`.

Since `||χ⁻¹v||≥||v||/K`, `W≥cI`, `c=δ/K²>0`. W is essentially bounded (for example `||W||≤δ⁻¹`). This c does not depend on the aperture.

The polarization equation is `L_RP=f|D_R`, `L_R=χ⁻¹-T_R`. Both multiplication and T_R are bounded on H_R=L²(D_R;C³). With the inner product conjugate-linear in its first slot,

`-Im⟨P,L_RP⟩=⟨P,WP⟩+Im⟨P,T_RP⟩≥c||P||²`.

The bounded sesquilinear form `a(Q,P)=i⟨Q,L_RP⟩` has real diagonal part at least c||P||². Complex Lax-Milgram supplies a unique solution for every f∈H_R and `||L_R⁻¹||≤c⁻¹`. This proves onto-ness, not merely a lower bound/injectivity. The form's boundedness constant may depend on R without changing the inverse estimate.

## 4. Exact outgoing weak Maxwell correspondence

For the integral solution P, define `u=g_k*P`, `E=f+k²u+∇div u`. Scalar elliptic regularity for `(Δ+k²)u=-P` gives u∈H²_loc; thus E∈L²_loc and `curl E=curl f+k²curl u∈H¹_loc`. Define the magnetic field by Maxwell's curl relation. The identity

`(curl curl-k²)(k²u+∇divu)=k²P`

holds in distributions, by `(Δ+k²)u=-P`. Inside D_R the integral equation gives E=χ⁻¹P, so P=χE. Therefore `curl curl E-k²εE=0` in all space. The distributional equation enforces the usual weak tangential interface conditions; no artificial surface current has been added at aperture edges. The construction has the outgoing vacuum far field.

Conversely any locally finite-energy outgoing weak solution of this material problem gives P=χE supported in D_R and lying in L². Subtract the same outgoing convolution. The difference solves entire homogeneous vacuum Maxwell equations in distributions. Taking divergence gives zero divergence; then all electric components solve homogeneous Helmholtz and are smooth by elliptic regularity. The outgoing uniqueness theorem in vacuum (Rellich/exterior continuation, equivalently the regular entire spherical-harmonic solutions cannot be outgoing) forces the difference to vanish. Thus the volume-integral and weak-Maxwell solutions coincide.

This direct tensor argument is needed: the abstract of Yurkin-Mishchenko 2018 explicitly concerns isotropic scatterers. Citing it alone would leave the arbitrary measurable tensor extension unsubstantiated. Here the scalar convolution and matrix multiplication proof supplies that extension under strict loss. The remaining classical tools are standard elliptic regularity, outgoing vacuum uniqueness, and complex Lax-Milgram, not new assumed electromagnetic conclusions.

## 5. Optical identities and reciprocity

The equation gives `⟨f,P⟩=⟨P,χ⁻¹P⟩* - ⟨P,T_RP⟩*` with the appropriate inner-product conjugations, hence

`σ_ext=k Im⟨f,P⟩`, `σ_abs=k⟨P,WP⟩`, `σ_sca=k Im⟨P,T_RP⟩=∫_{S²}|F_P|²`.

Consequently σ_ext=σ_abs+σ_sca. The absorption expression equals the material dissipation `k∫E†Im_Hχ E`. Reciprocity uses the bounded bilinear form `[u,v]=∫uᵀv`, without complex conjugation. Distributional T_R is transpose symmetric and χ⁻¹ is transpose symmetric, so `[u,L_Rv]=[L_Ru,v]`; applying this to solved currents gives a symmetric inverse. Since f₋=bar f₊, the two forward overlaps, and therefore the two extinctions, agree. Positive W and nonzero f imply positive extinction.

## 6. Outgoing transverse fibers and the grazing circle

Use transverse Fourier convention `hat g(κ)=∫exp(-iκ·x)g(x)dx`, inverse factor (2π)⁻². The outgoing Weyl fiber is

`β(κ)=sqrt(k²-|κ|²)` with β positive real for |κ|<k and positive imaginary for |κ|>k;

`Gκ(s)=i exp(iβ|s|)/(2β)`.

This is the distributional outgoing resolvent boundary value. Its singularity at the circle is locally integrable; it is not an additional delta measure there. It can also be obtained first for k+iε, then by the locally integrable boundary limit. Derivatives are `∂sGκ=-sign(s)exp(iβ|s|)/2` and `∂s²Gκ=-β²Gκ-δ₀`. On H=L²((0,L);C³), after zero extension in z, the fibers are:

* transverse entries `(k²δ_ab-κ_aκ_b)Gκ*`;
* mixed entries `iκ_a ∂sGκ*`;
* longitudinal entry `|κ|²Gκ*-I`.

On this fixed finite z interval their operator norms obey

`||Tκ||≤C[k,L](1+|κ|+(k²+|κ|²)/|β|)`.

At infinity this coarse bound is O(|κ|). Near |κ|=k it is O(dist(|κ|,k)^(-1/2)). Near zero β and all ordinary kernels are smooth and the local term cancels in the difference, so `||Tκ-T0||≤C0[k,L]|κ|` for |κ|≤k/2. Schur bounds of the finite-interval kernels and their κ derivatives justify these assertions.

The radial inverse-square-root singularity is L¹ on an annulus in R² but its square has a logarithmically divergent radial integral. This is why a global L² multiplier argument would fail. The manuscript avoids that argument. The counterexample audit explicitly demonstrates failures of stronger global-L² and uniform-Green assertions, without contradicting this theorem.

## 7. Planar problem and its complete two-direction power

At κ=0 the transverse block is convolution by `ik exp(ik|z-z'|)/2`, mixed blocks vanish, and the longitudinal block is -I. Its radiation form is

`Im⟨q,T0q⟩=k/4 (|∫exp(ikz)q⊥dz|²+|∫exp(-ikz)q⊥dz|²)≥0`.

The same strict-loss coercivity proves unique q solving `(χ⁻¹-T0)q=f`. Its longitudinal component and any transverse-longitudinal material coupling are retained. The outside field is an exact sum of the two propagating plane-wave amplitudes `b±=(ik/2)∫exp(∓ikz)q⊥dz`. This supplies

`A∞=k⟨q,Wq⟩`, `C∞=|b₊|²+|b₋|²`, `X∞=k Im⟨f,q⟩=A∞+C∞`.

For left incidence, the copolarized vacuum-relative transmission is `t_co=1+(ik/2)∫exp(-ikz)e†q dz`, giving `X∞=2(1-Re t_co)`. A boundary-plane transmission instead contains the extra vacuum phase exp(ikL); it must be removed. This prevents an incorrect phase-based comparison.

## 8. Smooth-window commutator in the correct norms

Fix g∈C_c^∞(Ω) and put g_R(x)=g(x/R). For q∈H define, in the distributional outgoing sense,

`H_R=T(g_Rq)-g_RT0q`.

Its transverse transform is `hat g_R(κ)(Tκ-T0)q`, with `hat g_R=R² hat g(Rκ)`. Split at |κ|=k/2.

At low frequency, Hilbert-valued Plancherel and the Lipschitz bound give

`||H_low||_{L²(R²;H)}≤C0||q||_H ||∇g_R||₂=C0||q||_H||∇g||₂`.

At high frequency, Schwartz decay gives, for R≥1 and N>3, `|hat g_R(κ)|≤C[g,N]R^(2-N)|κ|^-N`. The integral

`I_N=∫_{|κ|≥k/2}|κ|^-N (||Tκ||+||T0||)dκ`

is finite: at grazing use the L¹ square-root singularity; at infinity the radial bound is O(ρ^(2-N)). Bochner inverse Fourier integration gives

`sup_x ||H_high(x,·)||_H≤(2π)⁻² C[g,N] I_N R^(2-N)||q||_H`.

Restriction to RΩ multiplies by `R|Ω|^(1/2)`, so the high part is O(R^(3-N)) in L²(D_R). Thus `||H_R||_{L²(D_R)}=O_g(1)=o(R)`.

To justify the transform for an arbitrary H current, first use smooth compactly supported z approximants q_n. The low estimates give convergence in global transverse L²; the high estimates give convergence in L∞_x(H). For each fixed R, boundedness of restricted T on a finite support set identifies the limit with the original outgoing convolution restricted to D_R. Multiplication by g_R and T0 are bounded. This avoids imposing differentiability on q or asserting a globally square-integrable radiating field.

## 9. Current convergence and the two-step window limit

Inside D_R, `L_R(g_Rq)=g_Rf-H_R`. Hence the inverse estimate implies

`||P_R-g_Rq||≤c⁻¹(||(1-g_R)f||+||H_R||)`.

Adding `||(1-g_R)q||`, scaling x=Rξ, gives

`||P_R-q||≤R(c⁻¹||f||_H+||q||_H)||1-g||_{L²(Ω)}+c⁻¹||H_R||`.

For each fixed g, take the limsup after division by R. Smooth compactly supported functions are dense in L²(Ω), so the right-hand window error can be arbitrarily small. This establishes `||P_R-q||=o(R)`. The area factor |Ω| is fixed and positive. There is no exchange with δ→0, L→∞, or changing χ.

## 10. Observables, including all-angle scattering

The inverse bound gives `||P_R||≤c⁻¹||f||=O(R)` and the replicated q norm is O(R). Therefore

`|σ_ext,R-R²|Ω|X∞|≤k||f|| ||P_R-q||=o(R²)`;

`|σ_abs,R-R²|Ω|A∞|≤k||W|| ||P_R-q|| (||P_R||+||q||)=o(R²)`.

Apply **both** exact optical identities, compact and planar. The difference of their scattering powers is the extinction difference minus the absorption difference and is o(R²). The compact identity is a sphere integral derived in Section 2. Consequently the result includes edge diffraction, forward interference-relative scattering, polarization conversion, and all outgoing directions. A pointwise limit of F_R(n) is neither assumed nor necessary; the forward peak can narrow with R.

## 11. Quantitative square-aperture estimate

For S_R=(-R/2,R/2)² choose an interior smooth product cutoff transitioning over width w, 0<w≤R/8. Its departure from one is supported in a boundary strip of area O(Rw), giving `||1-g||₂≤C(Rw)^(1/2)`. Each derivative is O(w⁻¹) on that strip, so `||∇g||₂≤C(R/w)^(1/2)`. Fifth pure or mixed derivative L¹ norms are ≤CRw⁻⁴. For mixed derivatives the product estimate w⁻³ is absorbed by Rw⁻⁴ because w≤R. Five integrations by parts in a coordinate with `|κ_j|≥|κ|/sqrt(2)` yield `|hat g(κ)|≤CRw⁻⁴|κ|^-5`.

The low-frequency commutator is ≤C_low||q||(R/w)^(1/2). The high-frequency inverse transform is ≤C_high||q||Rw⁻⁴ uniformly in x, hence ≤C_high'||q||R²w⁻⁴ on the square. The current comparison becomes

`||P_R-q||≤C_edge(Rw)^(1/2)+C_low(R/w)^(1/2)+C_high R²w⁻⁴`,

where all constants are fixed for this k,L,χ,δ and may have different physical dimensions. Set ρ=kR, w=k⁻¹ρ^(1/3). For sufficiently large ρ this is admissible; the three geometric factors are respectively k⁻¹ρ^(2/3), ρ^(1/3), and k²ρ^(2/3). Consequently `||P_R-q||/R=O(ρ^(-1/3))`, with a fixed-stack dimensional prefactor. The same observable inequalities give the claimed area-normalized rate.

This exponent is a valid upper estimate, not a claim of optimality or a fitted numerical law. No constant uniform in weak loss or long thickness is established. Writing one C in the manuscript is acceptable after fixing units; separate constants as above make dimensional dependence explicit.

## 12. Compact supremum: required order of choices

For given k,P>1,Q>0 and ε>0, choose an integer plate index j satisfying its real cap. Choose a **finite** planar absorber and t so that its Γ exceeds 1-ε/3, using sufficiently small η<Q/2, sufficiently large but finite h, and t<1 sufficiently close to one. Add sufficiently small **fixed** δ>0 with δ<Q/2 to both layers; transfer-continuity keeps Γ above 1-2ε/3 and the real caps unchanged. Now susceptibility is invertible with fixed c>0. Only then let R grow, using the proved fixed-stack localization. The positive planar common extinction permits division of the converging cross sections. A sufficiently large **finite** R gives Γ>1-ε. This is an actual compact two-layer local, reciprocal, nonmagnetic dielectric body with positive-definite loss and the desired upper caps.

There is no assertion of a uniformly controlled aperture along the weak-loss sequence. The construction establishes a supremum, not an attained object, a bounded-size optimum, or a bandwidth law. The exact optical theorem excludes Γ=1 for any individual regular compact object with positive extinction.

## 13. Formal obligations still outstanding

Complete Lean verification would need actual three-dimensional vector-valued Sobolev/distribution definitions; the Helmholtz fundamental solution and outgoing uniqueness; bounded singular integral and Schur operators; exact weak-Maxwell/VIE equivalence; the full-sphere radiation and optical identities; transpose reciprocity; Bochner Fourier and resolvent boundary-value proofs; explicit fibers and estimates; the mixed-norm approximation argument; geometry/window scaling; planar tensor transfer synthesis, δ-continuity and the ordered compact construction. None may be replaced by an axiom named localization or by an abstract symmetric scattering matrix.

The new Lean components check generic coercivity/current-observable estimates and an explicit overlap certificate. They reduce future algebraic work but do not discharge these electromagnetic obligations. Thus Paper B's main results remain ordinary proofs, even though this audit supports their correctness.
