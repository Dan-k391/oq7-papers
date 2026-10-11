# OQ7 Lean verification

This is a real, compiled Lean project continuing the supplied OQ7 checkpoint. The full asymptotic Theorem 5.1 is **not yet proved**. Its exact statement is defined as `OQ7.Theorem51Statement` in `OQ7/Target.lean`; no proof or assumed replacement response model is supplied for it.

The actual finite physical class uses a list of homogeneous dielectric layers, `p + iq`, permeability one, vacuum exterior wave coordinates, `1 ≤ p ≤ P`, `0 ≤ q ≤ Q`, nonnegative widths, exact integrated loss `M`, exact transmitted power `T`, exact mean absorptance `a`, and total thickness including every layer. There is no fixed layer count, material catalogue, or positive minimum width. The response is computed from the exact layer-transfer product.

## Run on this PC

Open PowerShell in this folder:

```powershell
.\lake.ps1 build
.\verify.ps1 -Clean
```

`lake.ps1` uses the existing portable Lean installation from the earlier math-research-lab setup. `.lake/packages` is a directory junction to that setup's pinned package checkout. No system-wide installation or environment change was required. An independent machine can use the official `elan` toolchain manager, then `bootstrap.ps1`; the latter installs the pinned Lean toolchain, fetches the pinned dependencies, retrieves the official Mathlib cache, and verifies the project.

## Reproducible pins and proof integrity

- Lean/Lake: **4.34.1**, Lean commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (release `v4.34.1`).
- `lean-toolchain`, `lakefile.toml`, and the full `lake-manifest.json` preserve dependency versions.
- Every completed public theorem is imported by the default `OQ7` target and has `#print axioms` coverage.
- `verify.ps1` performs the actual build, independently enumerates kernel theorem constants, exports exact public theorem types, audits all theorem constants (including generated proof helpers), checks the compiler and every pinned dependency revision, and records source/configuration hashes.
- `-Clean` removes only this project's generated build directory before rebuilding. It keeps inherited Mathlib caches.
- Expected axiom dependencies are only Lean's standard logical foundations: `propext`, `Classical.choice`, and `Quot.sound`. No added mathematical axioms or native-evaluation axioms are accepted.

The primary `physical-theorem45` milestone passed for **408 public theorems** and **703 kernel theorem constants**. The latest `section5-physical-foundations` clean milestone passed for **550 public theorems** and **1,012 kernel theorem constants**, including generated helpers and Unicode theorem names. The independently rechecked original 118 declarations and their exact statements are archived in `verification/milestones/baseline-118/`. Theorem 4.5's finite estimates, uniform asymptotic bound, and varying-stack sequence lower limit are kernel-verified for the original physical class. Actual current results are in `verification/report.json`, `verification/build.log`, `verification/statements.log`, and `verification/axioms.log`. A proof is complete only when these checks pass. A defined proposition is not a proved theorem.

## Completed work

| Module | Proved content |
| --- | --- |
| `TwoPort` | Explicit reciprocal scattering matrix, actual absorption matrix, absorptances, determinant and coordinate identities. |
| `Envelope` | Strict active-branch parameter properties, exact tangent remainder, scalar deficit coefficient, determinant-budget bound. |
| `Passivity` | Matrix passivity consequences, reverse-triangle envelope bound, actual matrix deficit, and strict matrix gap conditional on a positive absorption determinant. |
| `Transfer` | Wave/field basis conversion, scattering boundary equations, reciprocity, absorption/flux congruence and determinant invariant, lossless-coating invariance. |
| `Layers` | Actual complex refractive index, finite homogeneous transfers and product order, determinant one, exact thickness/loss sums and resource cap. |
| `Fields` | Exact Maxwell and Helmholtz equations in each homogeneous layer, initial and transfer states, directed-flux derivative. |
| `Scattering` | Denominator bound and nonvanishing, nonzero transmission, passive reciprocal response from the field-flux defect. |
| `PhysicalPassivity` | Maxwell-derived flux monotonicity, positive semidefinite layer and finite-stack defects, actual finite-stack passivity and scattering existence. |
| `Phase` | The checkpoint's unit phase product, exact quadratic determinant penalty, and squared phase-distance remainder, without principal arguments. |
| `TargetBounds` | Actual exact-target class deficit, bounded asymmetry image, and both conditional supremum squeeze inequalities, without assuming attainment. |
| `StrictLoss` | Positive distributed loss implies positive definite actual absorption; every finite exact-target physical stack satisfies the strict Theorem 5.1 inequality `D < D0`. |
| `ResourceScalar` | Lemma 4.4: half-period convexity, separate full-period supporting tangent, polynomial bounds, exact sharp ratio limit, finite scalar aggregation. |
| `FourierCap`, `FourierSquare` | Lemma 4.2 with zero/full-period endpoint cases and arbitrary phases; exact full-square oscillatory identity. |
| `ResourceAsymptotics` | Ceiling counts, eventual small mean, exact scalar floor limit, and positive explicit half-period scalar floor. |
| `Gram` | Actual layer mixed-flux integration and the generic Gram determinant triangle identity. |
| `PhysicalGlobal` | Actual finite-layer partial transfers, interface continuity, global electric Maxwell derivative, magnetic Maxwell derivative away from finite interfaces, bounded measurable loss profile and exact integrated mass. |
| `PhysicalGram` | Actual scattering fields, true fundamental initial data, Wronskian and two-point electric wedge. |
| `PhysicalIntegrals`, `PhysicalAbsorption` | Actual mixed-flux telescoping, deposited absorption, full Maxwell Gram determinant with the transmission factor, and PSD exterior remainder. |
| `ModulusComparison`, `PhysicalModulus` | Lemma 4.1: finite-interface first-zero proof, initial modulus limits and actual physical fundamental solution comparison. |
| `FourierTriangle`, `FourierOpenCaps` | Exact oscillatory triangle identity and endpoint-insensitive capped Fourier bounds. |
| `GramProperties`, `DeterminantMinkowski` | PSD weighted Gram matrices, singular-inclusive determinant Minkowski and finite aggregation. |
| `ResourceCells`, `PhysicalCellBounds`, `ResourceCellsOpen` | Lemma 4.3 for actual scattering, including local open-interval caps independent of exterior materials. |
| `PhysicalClass`, `SelectedResource`, `ResourcePartition` | Arbitrary finite physical stack cap witnesses, original selected-interval class, exact target inclusion and equal-cell physical accounting. |
| `ResourceBounds`, `ResourceUniform`, `ResourceTheorem45` | Theorem 4.5's positive finite floor and genuinely uniform sharp asymptotic lower bound over varying actual stacks. |
| `PhysicalQuarterWave` | Section 5 physical lossless quarter-wave transfers, pair diagonal scaling, repeated blocks, thickness and loss accounting. |

The primary lower-bound objective is complete. The actual Maxwell model, Lemmas 4.1–4.4 and Theorem 4.5 passed a reproducible clean build and full axiom audit. Exact-target classes are proved to lie in the selected-resource class, using zero-loss vacuum padding under a thickness cap. Eventual nonemptiness and the matching upper asymptotic remain unproved.

## Remaining work toward Theorem 5.1

1. Instantiate the proved genuine Maxwell exponential factorization and exact core coefficients to finish the quintic cell remainder, repeated-core expansion and physical determinant asymptotic.
2. Exact matching via a real implicit-function theorem on all eight matrix entries, with exact target equalities and controlled coating changes.
3. Assemble the proved ordinary dielectric coating realization with the matched core sequence; prove eventual admissibility, exact targets, full thickness accounting and the unit-phase fourth-order remainder.
4. Discharge the actual construction hypotheses in `theorem51_of_physical_constructed_sequence`. The all-budget index and conditional supremum squeeze already compile; eventual nonemptiness and the sharp matching upper limit remain outstanding.

The source checkpoint remains authoritative for the detailed proof adaptations. `proof-progress.json` records successful clean milestones and exact remaining obligations, distinguishing missing formalization from detected mathematical defects.

## Sources and continuation

The original paper and checkpoint are preserved unchanged under `sources/`. Read `checkpoint.json` for the current status, `sources/original-checkpoint.md` for the audited target and detailed adaptations, then `verification/report.json` for the exact compiled theorem list. Keep unfinished obligations out of compiled theorem declarations; develop them in `work/` at the parent workspace until complete.

Official proof-validation guidance: [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

