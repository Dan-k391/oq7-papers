# Static Newtonian Fourier continuation — PARTIAL

The actual Newton kernel and its full distributional Hessian now have kernel-verified Fourier correspondence. **The requested identification of the physical volume operator with `staticFourierOperator` on currents is not complete. Physical Theorem 1.1 remains PARTIAL, with no proof declaration.**

This continues commit `6874b492e8d49d2303bb25aa12248b489c9ad13a`. Every Lean module present at that commit is preserved byte for byte. The aggregate import file only gains imports. `sources/pre-fourier-source-hashes.json` and `sources/pre-fourier-PrescribedExtinction.lean` record that baseline; its previous verification artifacts are preserved in `verification/milestones/pre-fourier/`. The original manuscript and exact physical target are unchanged. Historical contact and dyadic reports describe earlier states; this file supplies the current Fourier status.

## Assessment of the requested obligations

| Obligation | Assessment | Evidence and exact limitation |
| --- | --- | --- |
| Reuse the verified physical Newton Hessian and contact identity | PASS | `newtonTemperedHessian_scalarTest` identifies the actual tempered Hessian with the original `greenHessian 0 i j` on every original `ScalarTest`. `newtonTemperedHessian_contact_apply` retains the exact `−δᵢⱼ/3` contact term. |
| Exact Fourier multiplier, normalization and zero frequency | PASS for the physical kernel | `newtonTempered_fourier_eq` and `newtonTemperedHessian_fourier_eq` are equalities of actual tempered distributions on all complex Schwartz tests. The latter is the bounded function `−ξᵢξⱼ/‖ξ‖²`. Its entries equal those of the existing `staticSymbol`. |
| Physical Newton volume operator equals `staticFourierOperator` on a dense smooth current class | UNRESOLVED | No theorem yet connects convolution by this distributional kernel to the actual `outgoingVolumeDistribution 0 p`. Kernel correspondence does not prove operator equality on any current class. |
| Extend equality to actual compactly supported vector L² currents | UNRESOLVED | No physical Newton dyadic L² realization or current-operator equality is claimed. The existing Fourier operator contraction is preserved but cannot be used as a proved physical bound before identification. |
| Connect the dynamic remainder to the full outgoing Maxwell operator | UNRESOLVED; deferred | The preceding two operator obligations remain open. No new dynamic or aperture work was undertaken. |

## Exact principal declarations

All declarations are in `OQ7Prescribed`. `Position` is the existing three-dimensional real Euclidean space. The original `ScalarTest`, `ScalarDistribution`, `outgoingGreen`, `greenHessian`, `CompactPolarization`, `outgoingVolumeDistribution`, `staticSymbol`, `staticFourierOperator` and physical target statements have not been changed.

`NewtonFundamental.lean` derives the physical fundamental-solution trace from the existing contact identity:

```lean
theorem newton_laplacian_test_integral (φ : ScalarTest) :
    (∫ x : Position, newtonReal x * (testLaplacian φ) x) = -φ 0

theorem newton_hessian_trace_distribution :
    (∑ i : Fin 3, greenHessian 0 i i) = -newtonDirac
```

This is a consequence of integrable compensated principal values, not an assumed Poisson equation. It is not used to divide a distribution by `‖ξ‖²`.

`NewtonTempered.lean` bundles the **actual singular kernel** through its proved local L² part and bounded exterior part:

```lean
theorem newton_schwartz_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun x => φ x * outgoingGreen 0 x) volume

theorem newtonTempered_apply (φ : SchwartzMap Position ℂ) :
    newtonTempered φ = ∫ x : Position, φ x * outgoingGreen 0 x
```

`NewtonSchwartz.lean` proves compact smooth real tests are genuine complex Schwartz functions, their derivatives commute with complexification, and the kernel realizations agree:

```lean
theorem newtonTemperedHessian_scalarTest (φ : ScalarTest) (i j : Fin 3) :
    newtonTemperedHessian i j (scalarTestSchwartz φ) = greenHessian 0 i j φ

theorem newtonTemperedHessian_contact_apply (φ : ScalarTest) (i j : Fin 3) :
    newtonTemperedHessian i j (scalarTestSchwartz φ) =
      ((newtonPVValue φ i j - ((if i = j then 1 else 0) / 3) * φ 0 : ℝ) : ℂ)
```

The tempered Hessian is defined by the actual directional distribution derivatives of `newtonTempered`. It is not defined as an inverse Fourier transform of the desired symbol.

`NewtonTransform.lean` proves the global transform and Hessian correspondence:

```lean
theorem newtonTempered_fourier_eq :
    𝓕 newtonTempered = newtonFrequencyTempered

theorem newtonTempered_fourier_integral (φ : SchwartzMap Position ℂ) :
    𝓕 newtonTempered φ = ∫ ξ : Position, φ ξ * newtonFrequencyKernel ξ

theorem newtonTemperedHessian_fourier_integral
    (φ : SchwartzMap Position ℂ) (i j : Fin 3) :
    𝓕 (newtonTemperedHessian i j) φ =
      ∫ ξ : Position, φ ξ * ((-(ξ i * ξ j) / ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem newtonTemperedHessian_fourier_eq (i j : Fin 3) :
    𝓕 (newtonTemperedHessian i j) = newtonHessianFrequencyTempered i j
```

The frequency kernel and Hessian function are actual functions:

```lean
newtonFrequencyKernel ξ = (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)
newtonHessianFrequency i j ξ = ((-(ξ i * ξ j) / ‖ξ‖ ^ 2 : ℝ) : ℂ)
```

Their tempered representations have the corresponding actual integral as application. The first has proved local L¹ integrability at its inverse-square singularity and bounded exterior behavior. The second has proved global L∞ membership and norm at most one. Both products against Schwartz tests are proved integrable.

`NewtonSymbol.lean` connects the kernel coefficient to the existing tensor symbol:

```lean
theorem newtonHessianFrequency_staticSymbol (i j : Fin 3) (ξ : Position) :
    newtonHessianFrequency i j ξ = staticSymbol ξ (basisC j) i
```

This identifies the kernel entries, not the volume operator acting on currents.

## How normalization and zero frequency are proved

Mathlib uses the phase `exp(−2πi⟪x,ξ⟫)`. `NewtonFourier.lean` applies its proved tempered derivative identity twice, obtaining the factor `−4π²ξᵢξⱼ`. The actual scalar Newton transform supplies `(4π²‖ξ‖²)⁻¹`, so the constants cancel exactly.

The scalar transform is established directly by the positive-time heat representation:

\[
H_t(x)=(4\pi t)^{-3/2}e^{-|x|^2/(4t)},\qquad
N(x)=\int_0^\infty H_t(x)\,dt\quad(x\ne0).
\]

`NewtonHeat.lean` proves this integral using the reciprocal substitution and the Gamma integral, proves actual time integrability for every `x≠0`, and separately proves **non-integrability at the spatial origin**. The unrestricted Bochner integral's zero convention is not used as an integrability proof there.

`NewtonHeatPairing.lean` proves joint absolute integrability of `φ(x)H_t(x)` for each complex Schwartz test before using Fubini. The proof integrates its norm in time to `‖φ(x)N(x)‖` for `x≠0`, uses the previously proved integrability of this majorant, and removes the origin as a Lebesgue null set.

`NewtonHeatFourier.lean` uses Mathlib's Gaussian Fourier theorem to prove, for every `t>0` and every frequency, including zero,

\[
\widehat H_t(\xi)=e^{-4\pi^2t|\xi|^2},\qquad \int H_t=1.
\]

`NewtonFrequencyHeat.lean` proves the true exponential time integral for `ξ≠0`, proves joint absolute integrability against every Schwartz test using the actual locally integrable inverse-square frequency kernel, and justifies the second Fubini interchange. The resulting identity is on **all Schwartz tests**, so it does not leave an unidentified distribution supported at zero frequency.

`StaticSymbolCoordinates.lean` separately proves `volume {0}=0` and that assigning any continuous linear tensor value at the frequency origin gives the same actual L² multiplier. This null-set statement alone would not remove a Dirac or its derivatives from an unidentified distribution; the global heat-pairing proof supplies the required distribution equality.

## Exact remaining operator obligations

The absent target is the equality of the existing physical component distribution `outgoingVolumeDistribution 0 p i` with the distribution induced by coordinate `i` of

```lean
staticFourierOperator (p.memLp.toLp p.current)
```

for actual `p : CompactPolarization`. Neither this statement nor a conditional replacement has been declared as a proved theorem. Equality of the kernel entries is necessary but insufficient to obtain it.

The pinned Mathlib supplies the standard Fourier convolution theorem when **both factors are globally L¹**, Schwartz convolution, Schwartz density in L², L² Fourier/tempered compatibility, and compact smooth convolution regularization. The Newton kernel is not globally L¹, so applying that ordinary convolution theorem directly to it is invalid. No general tempered-distribution convolution implementation or direct actual-integral Fourier/L² compatibility theorem for L¹∩L² inputs was found in the pinned sources. These are gaps in the present implementation, not a claim that the underlying mathematics is impossible or that Mathlib's existing density theorems fail.

The smallest remaining reusable bridges are:

1. Prove absolutely integrable Fubini for the existing compact-current potential paired with an original test function, using the finite-radius cutoff. Identify the result with the Newton distribution acting on the **actual current/test correlation**.
2. Bundle that correlation as a genuine smooth compact function and prove differentiation/translation identities, including both Hessian derivatives. Compact L² inputs are also L¹; the correlation may permit a direct proof for this input class.
3. Prove compatibility between the actual Fourier integral of an L¹∩L² current and Mathlib's L² Fourier transform. Its tempered Fourier compatibility and integral-pairing uniqueness lemmas provide ingredients, but this compatibility is not yet a project theorem.
4. Prove coordinate and distribution compatibility with the existing vector `staticFourierOperator`. Establish physical equality on the smooth class and extend with genuine boundedness/density, or prove the stronger compact-current identification directly without changing the requested quantifiers.

Only after those bridges are proved may the existing Fourier contraction be transferred to the physical static operator. The distributional dynamic-minus-static identification, full outgoing dyadic realization, Maxwell existence/uniqueness, radiation identity, optical theorem, reciprocity, uniform aperture localization, grazing analysis, zero-angle limits, both exact-extinction arguments, positive-loss perturbation, and final theorem assembly remain unverified.

## Reproduction and proof evidence

Use the preserved pinned toolchain and dependencies:

```powershell
./configure.ps1
./verify.ps1 -Clean
./verify-milestones.ps1
```

Both verification scripts accept `-LeanBin` when the pinned Lean installation is not on PATH. `configure.ps1` accepts `-PackagesDirectory` to reuse exact pinned dependency checkouts. See the README for the unchanged reproducibility details.

`verification/clean-build.log` records the complete clean project build. `verification/milestones/` contains independent module build logs and exact declaration/axiom exports. `verification/statements.log` exports every named theorem and the preserved unproved physical target. `verification/axioms.log` contains transitive `#print axioms` for every public imported declaration in the two project namespaces, including generated constants. Private canonical names contain numeric name components that cannot be parsed as ordinary identifiers; they are audited directly with `Lean.collectAxioms`, the same transitive collector used by Lean's `#print axioms` command. `verification/Audit.lean` records both procedures, and the script requires an axiom report for every inventoried public or private constant.

The completed main Fourier declarations depend only on `[propext, Classical.choice, Quot.sound]`. There are no `sorry`, `admit`, custom mathematical axioms, native proof shortcuts, or unproved Fourier assumptions. The new modules compile without warnings; legacy style/deprecation warnings and generated-name warnings in the exhaustive audit are not suppressed. The unproved proposition `Theorem11Statement` is exported as a definition, and its axiom report is explicitly not a proof of the proposition.

The source gate, kernel inventory, axiom audit, dependency revision checks, original module hashes, manuscript hash and physical target hash are enforced by `verify.ps1`. Its status remains `PARTIAL`; the kernel Fourier flags are true, while both physical current-operator flags and the final physical theorem flag remain false. Declaration counts and a successful build are not presented as verification of the final claim.
