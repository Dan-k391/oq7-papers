# Newton contact and Fourier continuation — PARTIAL

**The full distributional contact identity is still unproved. The static Fourier and outgoing-operator identifications are still unproved. Physical Theorem 1.1 is still unproved.**

This continuation preserves every Lean module from commit `33dc4f5e9ed77ba8d7297584cda6f6bb76af0278` byte for byte. Only new modules and aggregate imports are added. Baseline hashes, the aggregate snapshot, and prior verification evidence are retained under `sources/pre-contact-*` and `verification/milestones/pre-contact/`. No aperture or extinction results are added.

The completed work addresses three of the exact missing contact dependencies: spherical second moments, angular boundary limits, and the convergence of the actual spherical principal value. None is asserted to imply the distributional Hessian identity without the missing integration-by-parts bridge.

## Actual measure and kernel

Positions remain `EuclideanSpace ℝ (Fin 3)`. The angular measure `sphereArea` is Mathlib's `volume.toSphere` on the actual unit sphere. The source proves orthogonal invariance, total area `4π`, and a polar-change integral formula with radial measure `volumeIoiPow 2`. It does not introduce an abstract measure with assumed moments. Equality with a separately defined Hausdorff surface measure is not a theorem in this continuation; the missing punctured-boundary formula must be proved using the specified polar measure or establish that correspondence.

The actual classical Newton Hessian kernel is

\[
C_{ij}(x)=\frac{3x_i x_j-|x|^2\delta_{ij}}{4\pi|x|^5},
\quad C_{ij}(0)=0.
\]

`newtonHessianKernel_classical` identifies it with the previously verified actual classical derivative of `outgoingGreen 0` off the origin. The global bound

\[
|C_{ij}(x)|\le \pi^{-1}|x|^{-3}
\]

is proved, with Lean's inverse convention at zero. The value at zero is irrelevant to the integrals, and is not a replacement for a Dirac contact term.

## Kernel-checked declarations

| Module | Main declaration | Exact completed obligation |
| --- | --- | --- |
| `SphereMeasure` | `orthogonalSphere_measurePreserving`, `sphereArea_real_univ` | Orthogonal invariance and area of the actual polar sphere measure |
| `SphereMoments` | `sphere_second_moment` | `∫ nᵢ nⱼ dσ = (4π/3)δᵢⱼ`, proved using coordinate reflections, swaps, and the unit norm |
| `SphereMoments` | `sphere_newton_angular_cancellation` | `∫ (3nᵢnⱼ−δᵢⱼ)dσ=0` |
| `NewtonBoundary` | `newtonContactBoundary_tendsto` | The actual angular contact boundary integral tends to `−δᵢⱼ φ(0)/3` |
| `NewtonBoundary` | `newtonDerivativeBoundary_tendsto` | The other angular boundary integral tends to zero |
| `NewtonPV` | `integral_polar_actual` | Actual volume integral equals its polar product-measure integral |
| `NewtonPrincipalValue` | `newtonCompensated_integrable` | Absolute integrability of the compensated singular kernel for every original test function |
| `NewtonPrincipalValue` | `newtonAnnulus_integrable`, `newtonAnnulus_integral_zero` | Absolute integrability and zero integral of each positive-inner-radius truncated radial annulus |
| `NewtonPrincipalValue` | `newtonPVTruncated_integrable` | Every positive-radius truncated kernel-times-test-function integral is integrable |
| `NewtonPrincipalValue` | `newtonPrincipalValue_tendsto` | The actual spherical principal-value limit exists and equals the specified compensated integral |

All theorems use the original `ScalarTest` space of real-valued smooth compactly supported test functions. No derivative, moment, integration-by-parts, Maxwell, or Fourier identity is an assumed property of these inputs. The Lipschitz bound used in the compensation argument is proved from their actual continuous derivatives and compact support.

The two verified boundary limits are for the concrete integrals

\[
B_{ij}(\varepsilon)
=-\frac1{4\pi}\int n_i n_j\varphi(\varepsilon n)\,d\sigma(n)
\longrightarrow -\frac{\delta_{ij}}3\varphi(0),
\]

\[
D_{ij}(\varepsilon)
=-\frac{\varepsilon}{4\pi}\int n_j\partial_i\varphi(\varepsilon n)\,d\sigma(n)
\longrightarrow 0.
\]

Here `∂ᵢφ` is the actual test-function derivative. Continuity of parameterized integrals over the compact sphere proves these limits, together with the exact second moments. They hold as real ε tends to zero, so in particular from positive radii. The proof does not assert that these expressions already equal boundary contributions of a proved volume integration identity.

For principal values the source defines the concrete, absolutely integrable function

\[
F_{ij,\varphi}(x)
=C_{ij}(x)\bigl[\varphi(x)-\varphi(0)1_{\{|x|\le1\}}\bigr].
\]

Its norm is bounded by a proved finite constant times `|x|⁻²`, and it has compact support. The source proves, for every ε>0,

\[
\int_{|x|>\varepsilon}C_{ij}(x)\varphi(x)\,dx
=\int_{|x|>\varepsilon}F_{ij,\varphi}(x)\,dx.
\]

The annular correction vanishes by actual polar change of variables and angular cancellation. Both integrals are proved integrable; equality is not inferred from the fallback value of an undefined Bochner integral. Dominated convergence then proves

\[
\lim_{\varepsilon\downarrow0}
\int_{|x|>\varepsilon}C_{ij}(x)\varphi(x)\,dx
=\int F_{ij,\varphi}(x)\,dx.
\]

The general radial cancellation lemma is valid for Mathlib's Bochner integral even when the integral is undefined in the analytic sense. Its use for annuli is accompanied by the separate positive-inner-radius integrability theorem. No physical identity is drawn from undefined-integral fallback behavior.

`newtonPVValue` is currently an integral-valued functional on the original test functions. It is **not yet bundled as a continuous distribution**, and its continuity in the test-function topology is not claimed. Pointwise principal-value convergence for all tests is the completed result.

## Precise remaining identities

| Requested obligation | Assessment |
| --- | --- |
| Actual spherical second moments | PASS |
| Angular contact and derivative boundary limits | PASS |
| Actual spherical principal-value convergence and truncated integrability | PASS |
| Punctured-ball integration by parts | UNRESOLVED |
| Full Newton distributional Hessian with `−δᵢⱼ/3` Dirac term | UNRESOLVED |
| Static Fourier multiplier equals Newton distributional volume operator | UNRESOLVED |
| Verified dynamic remainder equals distributional outgoing-minus-static difference | UNRESOLVED |
| Full bounded physical dyadic operator on compact-domain vector L² | UNRESOLVED |
| Physical Theorem 1.1 | UNRESOLVED / PARTIAL |

The next missing finite-radius identity, for every ε>0 and every original test function, is exactly

\[
\int_{|x|>\varepsilon}\frac1{4\pi|x|}
\partial_j\partial_i\varphi(x)\,dx
=\int_{|x|>\varepsilon}C_{ij}(x)\varphi(x)\,dx
+B_{ij}(\varepsilon)+D_{ij}(\varepsilon).
\]

The signs use the inward radial normal of the excluded ball. This formula is displayed as a **remaining proof obligation**, not installed as an axiom, structure field, hypothesis, or proved declaration. A proof must justify two integrations by parts on the punctured domain and the vanishing of an outer boundary term from compact support. An equivalent smooth radial-cutoff proof is also possible, but its derivative terms and limits must be proved.

Together with a proved limit of the left-hand side and the completed principal-value and boundary limits, that formula would yield the still-unproved exact evaluation identity

\[
\texttt{greenHessian 0 i j}\,(\varphi)
=\left(\texttt{newtonPVValue}\,(\varphi,i,j)
-\frac{\delta_{ij}}3\varphi(0)\right)_{\mathbb C}.
\]

The corresponding equality of continuous distributions is not inferred from the classical Hessian, the second moments, or the boundary limits alone.

After this bridge, the remaining Fourier work is still substantive: establish the singular Newton Hessian Fourier correspondence on a suitable dense smooth class with Mathlib's normalization, identify its action on actual compact vector L² currents with the existing `staticFourierOperator`, and extend the equality. Neither the expected symbol nor its already-proved norm bound gives that correspondence.

For the outgoing operator, still prove that the dynamic-minus-static distribution is the function distribution of the previously verified classical remainder, justify differentiation/convolution by integrable test-function arguments, and identify `outgoingVolumeDistribution` with static Fourier action plus the actual remainder convolution. Only then assemble the full compact-domain bounded operator through zero extension and restriction.

## Infrastructure and reproduction

This continuation implements the missing sphere invariance, normalization, polar integral bridge and singular principal-value convergence using pinned Mathlib infrastructure. The remaining immediate infrastructure gap is the punctured integration-by-parts identity above, or the corresponding cutoff argument. Mathlib's whole-space line-derivative integration-by-parts theorem can support the latter, but its hypotheses and cutoff limiting terms have not been discharged here. General box divergence formulas do not directly supply the displayed spherical-boundary formula.

Reproduce with the existing pinned configuration:

```powershell
./configure.ps1
./verify-milestones.ps1
./verify.ps1 -Clean
```

Both verification scripts accept `-LeanBin`; configuration accepts `-PackagesDirectory`. Lean remains 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency revision is changed.

Independent declaration/build/axiom logs are under `verification/milestones/spherical-moments/`, `newton-boundary/`, and `newton-principal-value/`. `verification/statements.log` exports every exact theorem declaration and the unchanged physical target definition. `verification/axioms.log` exports transitive axioms for all imported project declarations and generated constants. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; there are no custom axioms or proof holes.

The complete project rebuild cleans project artifacts and retains the pinned dependency cache. Its log preserves warnings from unchanged legacy sources. The new modules emit no build warnings. Previous source hashes, the supplied manuscript and physical target are checked. The report explicitly records `newtonContactIdentityVerified: false`, `staticNewtonIdentificationVerified: false`, and `theorem11Verified: false`. Build success and declaration counts do not verify any of those missing identities.
