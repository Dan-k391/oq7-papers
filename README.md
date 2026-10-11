# OQ7 prescribed extinction — PARTIAL Lean formalization

**Theorem 1.1 has not been kernel-verified. No final proof declaration exists.**

The continuation proves the **physical static and outgoing volume operator
identifications**, the **full contact identity**, and **actual global locally-L²
source fields satisfying both physical weak curls and the full uniform
Silver–Müller radiation condition** for every compact L² polarization.
The exterior convolutions are rigorously identified with the global source
representatives. See [OUTGOING.md](OUTGOING.md) for declarations and evidence.
Material scattering solvability and uniqueness, radiation power identities,
uniform aperture localization, and the prescribed-extinction construction
remain unverified. These are required before Theorem 1.1 can be proved.

The physical Newton volume operator equals `staticFourierOperator` for every compactly supported vector L² current, retaining the full contact Hessian. See [STATIC.md](STATIC.md) and [FOURIER.md](FOURIER.md). Apart from the documented smooth-test annotation correction in Maxwell.lean, every Lean module from commits `6874b492e8d49d2303bb25aa12248b489c9ad13a` and `8301dda82eaf84611a4a40982f77dc2787b16861` is preserved byte for byte.

The existing library and theorem quantifiers are preserved; the smooth-test annotation correction is documented below. [CONTACT_IDENTITY.md](CONTACT_IDENTITY.md), [CONTACT.md](CONTACT.md), [DYADIC.md](DYADIC.md), [FOUNDATIONS.md](FOUNDATIONS.md), and the correspondence table below preserve historical milestones; their former contact and outgoing-source gaps are closed by the latest source. No conditional substitute is advertised as Theorem 1.1.

`OQ7Prescribed.Theorem11Statement : Prop` is a **definition of an unproved proposition**, not a theorem. Its `#print axioms` output audits the definition's dependencies. It does not certify that the proposition is true.

## Sources and preservation

- `sources/OQ7_prescribed_extinction_2026-10-11.pdf` is a byte-for-byte copy of the supplied 19-page manuscript. SHA256: `3D9775D849234E828370D7C96D8BDCDD574BEB6831A7906EA6B7706579868710`.
- `OQ7/` and `OQ7.lean` preserve all Lean sources from the existing repository. Their original hashes are in `sources/legacy-source-hashes.json` and are checked by `verify.ps1`.
- `sources/legacy-README.md` preserves its original documentation. That README's completion status is stale: the actual source contains `OQ7.theorem51`.
- The legacy theorem concerns one-dimensional scalar dielectric stacks, their exact transmission and mean absorptance targets, and a resource asymptotic. It is not this manuscript's compact three-dimensional prescribed-extinction theorem. The namespaces remain separate.
- The preceding informal audit and its numerical diagnostics supplied useful locations to investigate. Neither audit judgments nor floating-point agreement are imported as Lean assumptions. Copies of the diagnostics are under `sources/audit-diagnostics/`.

## What is actually checked

| File | Kernel-checked content | Limit of the result |
| --- | --- | --- |
| `PrescribedExtinction/Basic.lean` | Euclidean three-dimensional coordinates, norms and pairings; transpose reciprocity of real-axis rank-one tensors; unit rotated axis; zero susceptibility outside the slab | Constitutive algebra only |
| `PrescribedExtinction/Materials.lean` | Exact rank-one tensor action, Cauchy bound, exact real and imaginary quadratic forms, and all material inequalities for `(1+iν)I+(a+ib)uuᵀ` under explicit scalar bounds | Does not establish how physical solutions change with ν |
| `PrescribedExtinction/Geometry.lean` | The slab lies in a finite closed ball; its closure is compact; exterior permittivity is vacuum; admissible layer tensors give pointwise transpose reciprocity | Does not prove electromagnetic reciprocity |
| `PrescribedExtinction/Maxwell.lean` | Unit incident amplitude, conjugacy of the two incident electric fields, unit spherical directions | Maxwell equations, outgoing condition and power expressions are definitions here; their analytic consequences remain open |
| `PrescribedExtinction/Drive.lean` | Exact absorber projection zero, plate projection `sin θ` times the phase, and exact zero-angle projected drive | Does not prove solution or power factorization, or uniformity as θ tends to zero |
| `PrescribedExtinction/GreenKernel.lean` | Local L¹ and local L² integrability of `exp(ik|x|)/(4π|x|)`; its genuine test-function distribution; full distributional Hessian and dyadic test formula | The Newton principal-value/contact formula is proved in `NewtonContact`; the positive-frequency formula and Helmholtz fundamental-solution identity remain open |
| `PrescribedExtinction/VolumePotential.lean` | The actual convolution exists at every point for compact vector L² currents; finite bounds on bounded regions; local integrability; full distributional volume formula and additivity | The differentiated potential is not yet realized as a bounded L² operator or identified with physical scattered fields |
| `PrescribedExtinction/StaticFourier.lean` | The explicit symbol `-ξξᵀ/|ξ|²` gives an L² contraction by Mathlib's unitary Fourier transform; its imaginary quadratic form vanishes | Physical Newton identification is proved in `NewtonStaticIdentification`; outgoing passivity remains unproved |
| `PrescribedExtinction/NewtonContact.lean` | Actual finite-radius Newton double integration by parts, exact contact coefficient, PV continuity and equality of continuous distributions, using the original tests and actual polar measure | Kernel Fourier identification is now proved in `NewtonTransform`; current-operator identification and the full physical Maxwell operator remain open |
| `PrescribedExtinction/NewtonTransform.lean` | Actual scalar Newton and full contact Hessian Fourier identities on all Schwartz tests; heat representation, genuine joint integrability, exact Gaussian normalization and zero-frequency treatment | Physical current-operator equality is proved in `NewtonStaticIdentification`; full outgoing realization remains open |

See [STATIC.md](STATIC.md) for the current proof frontier. Independent builds and `#print axioms` exports are under `verification/milestones/`. All earlier verification snapshots, including `pre-fourier/` for commit `6874b49`, are preserved. All previous Lean modules are checked byte-for-byte, except for exactly the archived smooth-test annotation correction in the physical target, by `verify.ps1`; the aggregate import file only gains appended imports.

There are no `sorry`, `admit`, custom mathematical axioms, or native proof shortcuts in the project sources. The verification script checks source gates and exports transitive `#print axioms` reports for every public imported declaration in both project namespaces, including definitions and generated constants. It also checks every private constant directly with `Lean.collectAxioms`, the collector used by `#print axioms`; this avoids parsing private canonical names with numeric components. Permitted foundational axioms are Lean/Mathlib's `propext`, `Classical.choice`, and `Quot.sound`.

## Concrete physical target

Positions are `EuclideanSpace ℝ (Fin 3)`, electric and impedance-normalized magnetic fields take values in `EuclideanSpace ℂ (Fin 3)`, and permittivities are complex `3×3` matrices. A `TwoLayerBody` has positive finite square aperture and two positive finite thicknesses, one constant tensor per layer, and vacuum outside. No common bound on dimensions or lower bound on loss occurs in the target.

`MaterialAdmissible P Q ε` imposes transpose symmetry and the real and imaginary quadratic-form versions of `I ≤ Re_H ε ≤ P I` and `0 < Im_H ε ≤ Q I`. The strict lower loss inequality applies to every nonzero complex vector.

`ScatteringState k B σ` contains actual locally square-integrable electric and magnetic fields satisfying the two distributional curl equations for `μ=I`, with uniform Silver–Müller radiation for their scattered parts and globally square-integrable compactly supported polarization. It contains no assumed optical theorem, reciprocity conclusion, inverse bound, or cross-section equality. Its mathematical regularity and equivalence to the volume-integral formulation are still proof obligations.

Cross sections use unit-electric-amplitude opposite plane waves. Absorption is local dielectric dissipation, extinction is optical work, and the current far field is integrated over all spherical angles using its full vector norm. The equality of this radiation integral with outgoing Poynting flux is unproved. Likewise, the spherical-coordinate formula's identification with surface measure, integrability of all expressions on physical solutions, and the equivalence of the weak formulation with the manuscript's physical formulation require proofs.

The target retains all positive-frequency, material-cap, positive prescribed-extinction and approximation-tolerance quantifiers. It requires both scattering states in the same body, both optical-work extinctions **exactly** equal to the prescribed target, and `1-ε < Γ < 1`. See `verification/statements.log` for the elaborated target and exact statements of every new theorem.

## Unverified dependencies and proof frontier

The following are **UNVERIFIED in Lean**, irrespective of the preceding informal audit's assessment. Page numbers refer to the supplied PDF.

| Manuscript obligation | Remaining formal work |
| --- | --- |
| §2, equations (5)–(8), PDF p.4 | The actual Newton kernel and contact Hessian Fourier identities are proved, in addition to the contact, convolution and classical remainder results. Static physical volume-operator identification on all compact vector L² currents is now proved. Still prove the positive-frequency Helmholtz fundamental-solution identity and outgoing identification, distributional remainder identification, bounded full L² realization/restriction, and equivalence to outgoing weak Maxwell solutions. |
| §2, equations (6)–(7), and §1 equation (2), pp.3–4 | Prove far-field asymptotics, all-channel radiation identity, forward optical theorem, positivity, integrability and power balance. No electromagnetic identity is a structure assumption. |
| §1 and §2, pp.3–5 | Prove Lorentz reciprocity for these rough coefficients and outgoing states, including exact equal extinction for the two plane waves. Matrix transpose symmetry alone is insufficient. |
| Lemma 2.1 and §2.1, pp.4–5 | Prove the complex coercive inverse, uniform aperture/angle bound, continuity and physical rank-one response factorization. Only the finite-dimensional material action and projected drive have been proved. |
| Theorem 3.1, §3.1–3.2, pp.5–6 | Construct the Weyl fibers with outgoing branches, treat the grazing `|ρ-k|⁻¹/²` singularity without an invalid L² multiplier step, prove cutoff localization uniformly down to θ=0, and transfer the estimate to optical work, dissipation and every outgoing angular channel. |
| §4 and Appendix A/B, pp.7,18 | Connect the planar transfer design to Maxwell fields; establish the normalized zero-angle and zero-plate-loss continuity, the lossless values, the absorber limit, and positivity of the planar normalization. Exact vanishing of the unnormalized drive at θ=0 is not this result. |
| §5.1, PDF p.8 | Prove continuity of finite-body extinction in θ and the two asymptotic endpoint inequalities at θ proportional to 1/R, with fixed loss and uniform constants. Apply IVT to the **actual physical extinction**. Mathlib has the scalar IVT; that does not establish these hypotheses. |
| §5.2, pp.8–9 | Prove the full Maxwell solution inverse identity and its boundedness; establish uniform solution and cross-section continuity under added isotropic loss at fixed finite aperture; preserve both endpoint inequalities and the asymmetry estimate; apply a second physical extinction IVT. Only the perturbed tensor inequalities are proved. |
| §4–5, pp.7–9 | Formalize the order of loss, thickness, angle-interval, aperture and perturbation choices, with every constant's parameter dependence; assemble the witnesses with exact extinction. |
| Lemma 1.2, PDF p.3 | Derive strict nonattainment from passivity, continuous far field, vanishing scattering and the optical theorem. |

Consequently neither `Theorem11Statement` nor existence of any admissible scattering witness satisfying its conclusions is proved by this project. A theorem about an arbitrary abstract response operator or free power variables would not close this frontier and has not been substituted for it.

## Reproduce

Pins:

- Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All transitive dependency revisions are saved in `sources/pinned-lake-manifest.json` and checked by `verify.ps1`.

On a machine with the pinned Lean toolchain available and network access for missing dependency checkouts:

```powershell
./configure.ps1
./verify-milestones.ps1
./verify.ps1 -Clean
```

If Lean is not on PATH, supply `-LeanBin 'C:\path\to\lean-4.34.1-windows\bin'` to `verify.ps1`. To reuse an existing checkout of the exact pinned dependencies:

```powershell
./configure.ps1 -PackagesDirectory 'C:\path\to\existing\.lake\packages'
./verify-milestones.ps1 -LeanBin 'C:\path\to\lean\bin'
./verify.ps1 -LeanBin 'C:\path\to\lean\bin' -Clean
```

`configure.ps1` restores the canonical saved manifest and optionally changes only the package directory. It does not upgrade dependencies. The locally generated `lake-manifest.json` is ignored by Git because it may contain a machine-specific cache path; the canonical pinned manifest is tracked. Do not run an unrestricted dependency update as part of reproduction.

Standard Lake commands work after configuration:

```text
lake build
lake env lean verification/Statements.lean
lake env lean verification/Audit.lean
```

The source repository excludes cached build artifacts and package checkouts. Fresh builds may need to compile dependencies. The saved `verification/clean-build.log` records a clean build of the complete project, and `verification/build.log` records the latest build. The report checks that the saved clean build used identical Lean sources. `verification/axioms.log` records all project constants; `verification/inventory.log` records the kernel inventory; and `verification/report.json` explicitly records `status: PARTIAL`, `theorem11Verified: false`, and `finalTheoremDeclaration: null`. Inventory counts are bookkeeping, not evidence that any missing analytic dependency or the target has been proved.

This repository is an incremental formalization artifact, not a proof of OQ7 or Theorem 1.1.

The continuation corrects the weak-curl test regularity from untyped top
(analytic in this Mathlib) to explicit ENat top (all smooth tests). The exact
Theorem11Statement body and all physical parameters are unchanged. The original
source is archived at verification/physical-target-before-test-correction.txt;
the verifier permits exactly this one annotation edit. TestRegularity.lean
proves the corrected condition implies the original analytic-test condition.
This strengthens the equations and avoids vacuous compact analytic testing.
