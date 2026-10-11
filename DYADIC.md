# Physical dyadic Green milestone — PARTIAL

The requested milestone is **incomplete**, and physical Theorem 1.1 is **unproved**. The existing target and every previous Lean module are preserved byte for byte. Only imports are appended to the aggregate `PrescribedExtinction.lean`. The baseline is commit `41ca4f4ff48bbe6d2d1a356e938f1d689bd111cf`; its source hashes and verification evidence are retained in `sources/pre-dyadic-source-hashes.json` and `verification/milestones/pre-dyadic/`.

No aperture-localization or extinction argument was added. No scattering result, contact identity, Fourier identification, or operator-representation identity is supplied as an assumption.

## Completed reusable dependencies

All positions and fields below are the existing actual three-dimensional Euclidean spaces. Write `r=|x|`, `z=ikr`, `g_k(x)=exp(ikr)/(4πr)` and

\[
H(s)=4+s+(s^2+4s+4)e^s.
\]

The actual kernels are assigned zero at the origin by Lean's inverse/division conventions.

| Module | Exact proved content | Boundary of the claim |
| --- | --- | --- |
| `RadialCalculus` | Fréchet derivative of the norm away from zero and first/second directional derivatives of `F(|x|)` | Radial derivative hypotheses are explicit mathematical hypotheses; the actual Green kernels satisfy them in the following modules |
| `NewtonKernel` | Actual first/second Newton radial derivatives and `∂ᵢ∂ⱼg₀(x)=(3xᵢxⱼ-r²δᵢⱼ)/(4πr⁵)` for `x≠0` | Classical differentiation; no principal value or contact theorem |
| `OutgoingRadial` | Actual radial derivatives of `g_k` and its classical Hessian for every real `k`, `x≠0` | No differentiation through the origin |
| `GreenCancellation` | Global, rigorous complex-exponential Taylor remainder inequalities and both cancellations used below | No numerical approximation |
| `DyadicRemainder` | Actual continuous-linear-map-valued classical kernel `D_k=(k²I+Hess)g_k` away from zero, exact cancellation formula for `R_k=D_k-D₀`, measurability and the operator-norm bound below | Equality with the full distributional Green kernel remains unproved |
| `RemainderConvolution` | Cutoff kernel is in vector-operator L², explicit cutoff seminorm estimate, actual remainder convolution exists at every point, is a.e.-invariant in the current, additive and complex homogeneous, and has the compact-domain L² estimate below | This is the classical remainder convolution, not yet the full distributional Maxwell operator |

`classicalDyadic_coordinate` proves that each matrix entry of the actual operator-valued kernel equals `k²δᵢⱼg_k` plus the actual double directional derivative at every nonzero point. Thus the estimate concerns a concrete kernel, rather than an arbitrary operator with an assumed bound.

The exact cancellation identity, implemented as `dyadicRemainder_cancel`, is

\[
R_k(x)=\left[\frac{k^2e^z}{4\pi r}
+\frac{e^z(z-1)+1}{4\pi r^3}\right]I
+\frac{e^z(z^2-3z+3)-3}{4\pi r^5}xx^T.
\]

The proved estimates are

\[
\|R_k(x)\|\le \frac{k^2}{4\pi}\,H(|k|r)r^{-1},
\qquad
\|R_k(x)\|\le \frac{k^2}{4\pi}\,H(|k|T)r^{-1}
\quad(\|x\|\le T).
\]

These hold for every real frequency; the all-point version interprets inverses at zero as zero. The envelope is nonnegative and increasing on nonnegative arguments. In particular, the classical remainder is locally L² in dimension three. For the cutoff used by the convolution,

\[
\|1_{B_T}R_k\|_2
\le k^2H(|k||T|)\|1_{B_T}g_0\|_2.
\]

For an existing `CompactPolarization` current `p` of support radius `a`, define the **actual** Bochner integral

\[
U_kp(x)=\int R_k(x-y)p(y)\,dy.
\]

`remainderPotential_integrable` proves its integrability at every `x`. If `K` is measurable and `|x|≤S` for every `x∈K`, `remainderPotential_eLpNorm_le` proves

\[
\|U_kp\|_{L^2(K)}
\le \|L\|\,\|p\|_2\,
\|1_{B_{S+a}}R_k\|_2\,|K|^{1/2},
\]

where the actual continuous bilinear evaluation map is `L(v,A)=Av`. The Lean statement uses `eLpNorm` and extended nonnegative real measure, so it also holds when `K` has infinite measure. For compact `K`, the bound is finite and `remainderPotential_memLp_on_compact` proves L² membership. For fixed support and output radii the constant is independent of the current's norm. Almost-everywhere changes to a current leave the convolution unchanged at every point. Additivity and scalar homogeneity are proved from the integral, without assumed linear response.

This gives a concrete compact-domain estimate for the **classical remainder**. It does not yet construct a continuous linear map on quotient compact-domain L² spaces for the **full physical** dyadic operator.

## Unverified obligations for this milestone

| Obligation | Assessment | Exact gap |
| --- | --- | --- |
| Exact Newton contact coefficient | UNRESOLVED | No proof of `∂ᵢ∂ⱼg₀ = pv[(3xᵢxⱼ-r²δᵢⱼ)/(4πr⁵)] − (δᵢⱼ/3)δ₀` in the existing test-function distribution space |
| Classical Newton/outgoing Hessians | PASS | Actual radial differentiation away from the origin, with every derivative hypothesis discharged for these kernels |
| Classical dynamic-minus-static estimate | PASS | Actual operator-norm estimate and cutoff L² bounds above |
| Actual classical remainder convolution bound | PASS | Every-point integrability, compact-domain L² estimate, a.e. invariance and complex linearity |
| Static distribution/Fourier identification | UNRESOLVED | Existing `staticFourierOperator` has not been shown equal to the Newton distributional volume potential |
| Distributional remainder identification | UNRESOLVED | No proof that the distributional dynamic-minus-static difference equals `Distribution.ofFun` of the checked classical remainder, with no extra singular contribution |
| Differentiation/convolution identification | UNRESOLVED | No test-function Fubini and differentiation theorem identifies `outgoingVolumeDistribution` with static Fourier action plus `remainderPotential` |
| Bounded full physical dyadic operator on compact-domain vector L² | UNRESOLVED | The preceding identifications and zero-extension/restriction realization remain missing |
| Physical Theorem 1.1 | UNRESOLVED / PARTIAL | No proof declaration exists; its full target proposition remains unchanged |

Equality of classical kernels away from the origin cannot discharge a distributional identity: a multiple of a Dirac mass is invisible there. Local L² membership of the remainder cannot by itself establish the absence of that contribution. Consequently neither the contact coefficient nor the full operator's boundedness is inferred from the completed estimates.

## Exact infrastructure frontier in pinned Mathlib

The inspected Mathlib revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`. It provides the following ingredients, but no directly usable result closing the following project obligations was found:

1. **Weak Hessian across a puncture.** `Analysis/Distribution/Distribution.lean` provides genuine distributional derivatives and locally integrable function distributions. `MeasureTheory/Integral/DivergenceTheorem.lean` and `Analysis/BoxIntegral/DivergenceTheorem.lean` provide box integration formulas. `Analysis/Calculus/LineDeriv/IntegrationByParts.lean` also provides whole-space integration by parts under integrability and derivative hypotheses; it can support a cutoff proof. A punctured-ball integration-by-parts theorem with normalized sphere boundary measure, or an equivalent smooth radial-cutoff weak-derivative theorem with its limiting estimates, still must be implemented. This is a missing proved bridge in this project, not a claim that general differentiation or integration by parts is absent from Mathlib.
2. **Normalized boundary limit.** `MeasureTheory/Constructions/HaarToSphere.lean` provides polar measure decomposition, and `MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean` provides ball volumes. Still prove the spherical second moments with normalization `∫ nᵢnⱼ dS=(4π/3)δᵢⱼ` and the test-function small-radius limits, or the corresponding cutoff annulus identities. These must supply the coefficient and principal-value convergence in the actual distribution space.
3. **Singular Fourier/distribution correspondence.** `Analysis/Fourier/LpSpace.lean` provides the unitary L² transform used by the existing multiplier. Still establish the Newton weak-Hessian Fourier identity on an adequate dense class and extend it to the actual compact vector L² currents. Defining a bounded multiplier with the expected symbol does not prove this correspondence.
4. **Kernel-to-volume identity.** The checked local integrability and convolution bounds support Fubini and approximation arguments, but those arguments connecting full distributional derivatives to static-plus-remainder action remain unimplemented. Establish them before assembling the quotient-space bounded operator.

The smallest dependencies implemented in this continuation are radial Hessian calculus, actual outgoing radial derivatives, rigorous exponential cancellation, and the resulting actual remainder convolution estimate. They close the analytic estimate part without assuming the singular distribution identities. The next proof should address item 1 and item 2; this continuation has not moved to aperture localization.

## Reproduction and evidence

Use the existing configuration and verification scripts:

```powershell
./configure.ps1
./verify-milestones.ps1
./verify.ps1 -Clean
```

Both verification scripts accept `-LeanBin`; `configure.ps1` accepts `-PackagesDirectory` to reuse checkouts at the exact pinned revisions. See README for pinned compiler and dependency setup. Independent new milestone logs are under `verification/milestones/radial-hessian/` and `verification/milestones/dyadic-remainder/`.

`verification/statements.log` contains elaborated declarations, including every new theorem and the unchanged target definition. `verification/axioms.log` exports transitive `#print axioms` for every imported project constant; the script rejects anything outside `propext`, `Classical.choice`, and `Quot.sound`. `verification/clean-build.log` records a complete project rebuild after cleaning project artifacts, while retaining the pinned dependency build cache. `verification/report.json` records the source hashes, preserved earlier sources, unresolved physical identifications, and `dyadicGreenMilestoneComplete: false`.

There is no `sorry`, `admit`, custom axiom or native proof shortcut. The target's axiom report is the report for a **definition of a proposition**, not for a proof. Build success and inventory counts do not verify the contact identity, the full Green operator or Theorem 1.1.

The complete clean rebuild retains style and deprecated-name warnings emitted by the unchanged legacy `OQ7/` sources. They are included in the log. The new kernel modules emit no build warnings. Exporting axioms for every generated auxiliary constant also emits Lean's auxiliary-name stability warnings; those exports are retained rather than omitted from the audit.
