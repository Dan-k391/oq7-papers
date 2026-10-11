# Foundational Maxwell continuation — PARTIAL

For the latest contact progress, see [CONTACT.md](CONTACT.md). The exact spherical moments, angular boundary limits and principal-value convergence are proved. The punctured integration identity, full distributional Hessian/contact identity and Fourier/outgoing correspondences remain unverified.

This document records the preceding three foundational modules. The latest continuation is documented in [DYADIC.md](DYADIC.md): classical Hessians, dynamic-minus-static cancellation and actual remainder convolution estimates are now proved. The distributional contact term and the identification and bounded realization of the full physical dyadic operator remain unproved.

The exact physical target `OQ7Prescribed.Theorem11Statement` is unchanged and unproved. No declaration of a proof of Theorem 1.1 exists. The additions below are intermediate analytic results for its actual kernel and current space; they are not an abstract replacement theorem.

## Independently compilable milestones

### 1. Actual outgoing scalar kernel and full distributions

`PrescribedExtinction.GreenKernel` uses three-dimensional Euclidean space and the function

\[
g_k(x)=\frac{e^{ik|x|}}{4\pi|x|}.
\]

Lean assigns the value zero at the origin. All distribution integrals are independent of a value at this null set. The norm formula, measurability, local integrability and L² membership on every compact set are proved, using the integrability of `|x|⁻¹` and `|x|⁻²` in dimension three.

`outgoingGreenDistribution` is Mathlib's continuous real-linear functional on smooth compactly supported real test functions, with complex values. Its integral formula is proved. Using Mathlib's genuine distributional derivatives, `dyadicGreenDistribution` defines

\[
D_{ij}=(k^2\delta_{ij}+\partial_i\partial_j)g_k,
\qquad
D_{ij}(\varphi)=k^2\delta_{ij}\int g_k\varphi
  +\int g_k\partial_j\partial_i\varphi.
\]

The second derivative is the full distributional derivative. This definition retains singular contributions; it does **not** prove their explicit coefficient or a principal-value formula. In particular, no contact-term theorem is claimed yet. Mathlib's `Distribution.ofFun` has a fallback for functions without proved integrability; every use here has local integrability proved and an explicit integral evaluation theorem.

Audit: `verification/milestones/green-kernel/axioms.log`.

### 2. Actual convolution and distributional volume potential

`PrescribedExtinction.VolumePotential` takes vector currents `p ∈ L²(ℝ³;ℂ³)` vanishing outside some finite ball. These are input-space conditions, not assumed Maxwell or power identities. Existing `ScatteringState` polarization currents are proved to belong to this class; the construction does not assert that any such scattering state exists.

The actual Bochner integral

\[
A_kp(x)=\int_{\mathbb R^3}g_k(x-y)p(y)\,dy
\]

exists at **every** point. To prove this, the kernel is cut off on a ball containing every contributing difference `x-y`, and Mathlib's L²–L² convolution estimate applies. For `|x| ≤ S` and support radius `r`, the checked finite bound is

\[
|A_kp(x)|\le \|L\|\,\|p\|_2\,
 \|1_{\{|z|\le S+r\}}g_k\|_2,
\]

where `L(v,z)=zv` is the continuous bilinear map used by Mathlib's convolution. The result holds for every real `k`, every such current and every bounded region. It proves local integrability of the potential. Equality of currents almost everywhere implies equality of the potential pointwise.

The source defines and proves the test formula and additivity for

\[
K_kp=(k^2I+\nabla\nabla\!\cdot)A_kp
\]

as a vector of genuine distributions. Its second derivatives have not been shown to be L² functions. A bound for `A_kp` does not give a bound for `K_kp`.

Audit: `verification/milestones/volume-potential/axioms.log`.

### 3. Explicit static Fourier operator

`PrescribedExtinction.StaticFourier` constructs a complex-linear continuous operator on actual vector L² using Mathlib's unitary Fourier transform:

\[
T=\mathcal F^{-1}M\mathcal F,
\qquad M(\xi)=-\frac{\xi\xi^T}{|\xi|^2},\quad M(0)=0.
\]

The source proves `‖M(ξ)‖ ≤ 1`, measurability of its action on each L² field, linearity, and `‖T‖ ≤ 1`. For every vector L² field `f`, it proves

\[
\operatorname{Im}\langle f,Tf\rangle_{L^2}=0.
\]

The imaginary part is passed through a proved integrable quadratic-form integral. This result concerns the explicit static operator only. Equality of `T` with the distributional Newton volume operator has **not** been proved. Passivity of the outgoing operator is also unproved.

Audit: `verification/milestones/static-fourier/axioms.log`.

## Remaining dependencies, in proof order

Every entry below is **UNVERIFIED**. None is an axiom or a hypothesis of a declaration purporting to prove the final theorem.

1. **Fundamental solution and explicit contact term.** Prove `(Δ+k²)g_k = -δ₀` in the chosen distribution space. Prove the spherical principal-value formula
   \[
   \partial_i\partial_jg_0
   =\operatorname{pv}\frac{3x_ix_j-|x|^2\delta_{ij}}{4\pi|x|^5}
    -\frac{\delta_{ij}}3\delta_0.
   \]
   The boundary/small-sphere terms and the meaning of this principal value must be justified, not inferred from the formal derivative definition.
2. **Bounded physical volume operator.** Identify the static distributional convolution with the checked Fourier operator. The classical derivatives, locally L² remainder estimate and actual remainder convolution bound are now proved; still identify that remainder with the full distributional difference and justify differentiation/convolution. Construct zero extension, restriction and a bounded realization of the full `K_k`, and prove it represents the distribution already defined. Track domain and frequency dependence.
3. **Outgoing passivity and physical solvability.** Establish the full-vector radiation formula for compact currents, with all spherical directions and the exact constants in the manuscript. Derive the nonnegative imaginary quadratic form of `K_k`. Prove the complex coercivity and surjectivity/inverse bound for `α⁻¹-J* K_k J`. Construct fields, prove the weak curl equations and Silver–Müller condition, and prove representation and uniqueness in the existing `ScatteringState` class. No state-existence theorem has yet been established.
4. **Cross sections, optical theorem and reciprocity.** Prove far-field asymptotics, integrability, the equivalence of the current radiation integral with flux, power balance and the optical theorem. Justify the spherical integration convention. Prove Lorentz reciprocity for the finite anisotropic body and the exact opposite-incidence extinction equality. Transpose-symmetric material tensors alone do not prove this equality.
5. **Rank-one response and uniform aperture localization.** Prove the actual Maxwell response factorization. Construct the Weyl fibers with the correct outgoing branch and contact term, control the grazing `||κ|-k|⁻¹/²` singularity, and prove cutoff localization uniformly in the rotation angle including zero. The grazing singularity is locally L¹ but cannot be used as a locally L² multiplier. Transfer convergence to absorption, optical work and every outgoing channel.
6. **Planar limits.** Link transfer solutions to the physical fields. Prove normalized zero-angle and zero-plate-loss limits, the planar design values, the absorber limit and positivity of the normalization. Exact zero projected drive at zero angle is insufficient for these normalized limits.
7. **Both exact-extinction arguments.** Prove physical solution and extinction continuity and the finite-aperture endpoint inequalities before using scalar IVT. After fixing a finite aperture, prove solution and power continuity under strictly positive isotropic loss, preserve the endpoint inequalities and asymmetry bound, and perform the second IVT. Mathlib's IVT alone does not establish any of those hypotheses.
8. **Final physical assembly.** Track the order and dependence of aperture, angle, thickness, material loss and perturbation choices. Derive strict nonattainment from the optical theorem and continuous far field. Produce admissible common-body witnesses for both incidences, exact positive prescribed extinction, and the required asymmetry for every parameter and tolerance in the unchanged target.

## Verification and preservation

Run `verify-milestones.ps1` to compile and audit each milestone separately, then `verify.ps1 -Clean` for a clean complete project build and the transitive axiom audit. Both accept `-LeanBin`. Dependency revisions remain pinned; legacy sources, the manuscript and the physical target source are hash-checked. Previous verification evidence is retained in `verification/milestones/initial-partial/`.

`verification/report.json` explicitly records the partial status and unresolved identifications. `verification/statements.log` exports the unchanged target and exact supporting statements. `verification/axioms.log` audits all project constants against only `propext`, `Classical.choice` and `Quot.sound`. Printing axioms for the target proposition audits a definition; it is not a proof of that proposition. Build success and declaration counts are not verification of Theorem 1.1.
