# Newtonian contact milestone — PASS; physical Theorem 1.1 — PARTIAL

The immediate Newtonian contact milestone is complete. The finite-radius punctured double integration-by-parts identity, both inward-normal coefficients, vanishing outer boundary terms, and the exact distributional Hessian identity are kernel-checked. The actual principal-value integral is bundled as a continuous distribution on the original test-function space.

**Physical Theorem 1.1 remains unproved. Fourier identification has not been advanced.** This milestone does not establish the positive-frequency outgoing contact formula, a bounded full Maxwell operator, or existence of scattering solutions.

Every previously verified Lean module from baseline commit `4c3b66d977a60dc3370808acc77aa545df289392` is preserved byte for byte. The aggregate import file only gains imports. Previous hashes, the aggregate snapshot, build logs, axiom exports and report are preserved in `sources/pre-punctured-*` and `verification/milestones/pre-punctured/`. The physical target and supplied manuscript retain their earlier hashes. `CONTACT.md` records the preceding PARTIAL state; this file supersedes its contact-status assessment.

## Exact declarations

All names below are in namespace `OQ7Prescribed`. `Position` remains actual three-dimensional Euclidean space, `ScalarTest` remains Mathlib's real smooth compactly supported test functions, and `ScalarDistribution` remains its complex-valued continuous distributions. `sphereArea` is the previously verified actual polar measure `volume.toSphere`, not an abstract measure with assumed moments.

The finite-radius identity is:

```lean
theorem newton_punctured_double_ibp
    (r : ℝ) (hr : 0 < r) (φ : ScalarTest) (i j : Fin 3) :
    (∫ x in {x : Position | r < ‖x‖},
      newtonReal x * (testPartial j (testPartial i φ)) x) =
      newtonPVTruncated φ i j r +
        newtonContactBoundary φ i j r + newtonDerivativeBoundary φ i j r
```

Here `newtonReal x = (4 * Real.pi * ‖x‖)⁻¹` and `newtonReal_eq_green` proves its complex embedding equals the original `outgoingGreen 0`. Every positive-radius truncated integral is proved integrable. The boundary terms are exactly the previously verified definitions, without modified signs or test functions.

The Hessian evaluation is:

```lean
theorem newton_hessian_contact_apply
    (φ : ScalarTest) (i j : Fin 3) :
    greenHessian 0 i j φ =
      ((newtonPVValue φ i j -
        ((if i = j then 1 else 0) / 3) * φ 0 : ℝ) : ℂ)
```

The principal-value distribution's `toFun` is the original actual compensated integral, embedded in ℂ. Its linearity and continuity are proved using the preceding evaluation identity and the continuous Hessian and Dirac distributions. They are not input assumptions. Its integral representation is definitional:

```lean
theorem newtonPVDistribution_apply (φ : ScalarTest) (i j : Fin 3) :
    newtonPVDistribution i j φ = (newtonPVValue φ i j : ℂ) := rfl

theorem newtonPVValue_continuous (i j : Fin 3) :
    Continuous (fun φ : ScalarTest => newtonPVValue φ i j)

theorem newton_hessian_contact_distribution (i j : Fin 3) :
    greenHessian 0 i j =
      newtonPVDistribution i j -
        ((if i = j then 1 else 0) / 3 : ℝ) • newtonDirac
```

`newtonDirac` is Mathlib's actual `Distribution.delta` at the origin mapped by `Complex.ofRealCLM`. `newtonDirac_apply` proves its value is `(φ 0 : ℂ)`. Distribution equality is proved by extensionality on all original test functions. The value of a kernel at the origin does not substitute for a Dirac distribution.

## Integration argument and signs

For fixed `r>0` and `t>0`, the proof uses the actual smooth radial cutoff

\[
\chi_{r,t}(x)=S((|x|-r)/t),\qquad S=\texttt{Real.smoothTransition}.
\]

It is zero inside the puncture, one beyond `r+t`, and lies in `[0,1]`. Its derivative is proved to be

\[
\partial_i\chi_{r,t}(x)
=t^{-1} S'((|x|-r)/t)x_i/|x|.
\]

At the origin the identity is justified by local equality to zero. The Newton kernel and its first derivative, multiplied by this cutoff, are globally C¹. Thus Mathlib's whole-space line-derivative integration-by-parts theorem applies to them and the original tests. All three integrability hypotheses for each application are discharged by continuity and compact support. No spherical divergence theorem is assumed.

`newton_cutoff_double_ibp` proves exactly

\[
\int\chi_{r,t}N\,\partial_j\partial_i\varphi
=\int\chi_{r,t}C_{ij}\varphi
+\int(\partial_i\chi_{r,t})(\partial_jN)\varphi
-\int(\partial_j\chi_{r,t})N\partial_i\varphi.
\]

The scalar `N`, its actual first derivative, and its actual classical Hessian are independently differentiated; their formulas are not assumed. Both derivative terms have support in the finite shell `r<|x|<r+t`. Their absolute integrability is proved before polar conversion and Fubini.

`integrable_polar_actual` and `integral_polar_iterated_actual` reuse Mathlib's measure-preserving polar homeomorphism and the radial density `s²`. The two shell terms reduce, respectively, to

\[
-\frac1{4\pi}\int_0^1 S'(u)
  \int n_i n_j\varphi((r+tu)n)\,d\sigma(n)\,du,
\]

\[
\frac1{4\pi}\int_0^1 S'(u)(r+tu)
  \int n_j\partial_i\varphi((r+tu)n)\,d\sigma(n)\,du.
\]

The radial rescaling is proved by Mathlib's interval-integral affine change of variables. The fundamental theorem of calculus gives the exact normalization `∫₀¹ S'=1`. Continuity of parameterized integrals on the compact interval, together with the earlier sphere-integral continuity, gives the fixed-radius limits. Dominated convergence gives the two exterior volume limits. Uniqueness of limits proves `newton_punctured_double_ibp` for every positive `r`.

`newton_inner_derivative_normal` proves the first inner boundary coefficient using the normal `−n`:

\[
r^2 N(rn)\partial_i\varphi(rn)(-n_j)
=-\frac r{4\pi}n_j\partial_i\varphi(rn).
\]

`newton_inner_contact_normal` proves the second:

\[
-r^2(\partial_jN)(rn)\varphi(rn)(-n_i)
=-\frac1{4\pi}n_i n_j\varphi(rn).
\]

`newton_outer_boundary_vanishes` proves that there is a finite positive `R` such that both angular boundary terms vanish for every outer radius `T≥R`. It bounds the union of the actual supports of `φ` and `testPartial i φ`; both functions vanish on those outer spheres. Whole-space integration by parts already removes outer contributions using compact support, and this additional theorem makes their spherical vanishing explicit.

Finally `newton_test_puncture_removal` proves convergence of the left side as `r→0`. The previously verified principal-value convergence, spherical moments, contact boundary limit and derivative boundary limit then imply `newton_contact_identity_real`. Embedding that identity in ℂ and using the original distributional derivative evaluation proves the full Hessian/contact identity. Continuity of the actual PV functional is deduced only after this bridge is complete.

## Verification and remaining work

| Obligation | Assessment |
| --- | --- |
| Finite-radius double integration by parts, actual Newton kernel and original tests | PASS |
| Inward-normal sign and both inner boundary coefficients | PASS |
| Vanishing outer boundary terms | PASS |
| Actual spherical PV and boundary limits imply exact `−δᵢⱼ/3` contact formula | PASS |
| PV continuity and equality in the actual distribution framework | PASS |
| Physical Theorem 1.1 | PARTIAL / UNVERIFIED |

Independent builds and exact declarations with transitive `#print axioms` are in `verification/milestones/newton-cutoff/`, `newton-shell/`, and `newton-contact/`. The complete project audit exports every project constant and generated declaration in `verification/axioms.log`, and every exact theorem statement plus the unchanged unproved physical target in `verification/statements.log`. The completed analytic theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. There are no proof holes, custom axioms, native shortcuts, or unproved physical assumptions.

Reproduce with the pinned configuration:

```powershell
./configure.ps1
./verify-milestones.ps1
./verify.ps1 -Clean
```

The scripts accept the existing `-LeanBin` option; configuration accepts `-PackagesDirectory` to reuse a pinned dependency cache. Lean is 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`. `-Clean` cleans all project build artifacts and retains cached pinned dependencies. Warnings in unchanged legacy modules remain in the logs. The newly added modules build without warnings.

`verification/report.json` records the completed contact obligations and preservation checks separately from `theorem11Verified: false`, `staticNewtonIdentificationVerified: false`, and `dyadicGreenMilestoneComplete: false`. A successful build or declaration count does not prove any missing theorem.

Still unverified, and not attempted beyond the requested stopping point:

1. Identification of the existing static Fourier multiplier with the actual distributional Newton operator, including normalization, a dense smooth class and extension to compact vector L² currents.
2. Distributional outgoing-minus-static identification with the verified classical remainder, the positive-frequency contact formula, and the scalar Helmholtz fundamental-solution identity.
3. The full bounded physical dyadic operator on compact-domain vector L² and equivalence of its volume formulation with outgoing weak Maxwell solutions.
4. Maxwell existence/uniqueness, passivity/coercivity, full radiation identity, optical theorem, reciprocity and reciprocal extinction equality.
5. Uniform inverse/response factorization, aperture localization including grazing channels and the uniform zero-angle limit.
6. Physical continuity and both exact-extinction intermediate-value arguments, strictly positive-loss perturbation, order of limits and final assembly of the exact physical Theorem 1.1.

No unresolved obligation in this list is packaged as an axiom, a hypothesis of an advertised final theorem, or an abstract response model. `OQ7Prescribed.Theorem11Statement : Prop` remains the same unproved physical target definition, and no final proof declaration exists.
