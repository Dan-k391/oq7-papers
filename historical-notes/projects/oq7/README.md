# OQ7 Lean verification

This project contains the full formal construction and proof of the supplied paper's physical Theorem 5.1. The exact proposition is `OQ7.Theorem51Statement` in [`OQ7/Target.lean`](OQ7/Target.lean); its proof is `OQ7.theorem51` in [`OQ7/SharpPhysicalConstruction.lean`](OQ7/SharpPhysicalConstruction.lean), with no additional construction hypotheses. The default `OQ7` target imports the complete proof.

**Consult verification/report.json for current verification status.** The build, exact theorem types, kernel inventory, dependency revisions, source hashes, and transitive axiom audit are recorded separately from this description.

## Exact physical result

Fix `k > 0`, `P > 1`, `Q > 0`, `M > 0`, `0 < T < 1`, and `0 < a < (1 - T²)/2`. The model is normal-incidence Maxwell propagation through finite lists of homogeneous dielectric layers, with scalar relative permittivity `p + iq`, permeability one, and identical vacuum exterior media. Each layer satisfies `1 ≤ p ≤ P`, `0 ≤ q ≤ Q`, and nonnegative width. Integrated loss is exactly `M`, transmitted power exactly `T`, and mean absorptance exactly `a`. Every layer's width, including spacers and matching coatings, counts toward the thickness budget. There is no fixed layer count, fixed material catalogue, or positive minimum width. Responses come from the actual finite layer-transfer product.

With `b = 1 - T - a`, `s = √(1 - 2a)`, `y₀ = s - T`, `x₀ = √(b² - y₀²)`, `D₀ = 2x₀`, and `α = T y₀/(s x₀)`, the theorem asserts:

- The exact-target physical class is nonempty for all sufficiently large real thickness budgets `L`.
- Every finite exact-target stack has absorptance asymmetry `D < D₀`.
- Its supremum `D*(L)` satisfies

  ```text
  lim L → ∞ (kL)² [D₀ - D*(L)] = α π² (kM)⁴ / (3 P Q²).
  ```

The construction uses actual admissible dielectric layers and exact target equalities. The supremum argument requires no maximizing stack. Lean certification concerns this mathematical model and formal statement; it does not establish experimental performance or a novelty claim.

## Run and reproduce

Open PowerShell in this folder:

```powershell
.\lake.ps1 build
.\verify.ps1 -Clean
```

On this PC, `lake.ps1` selects the portable compiler from the earlier math-research-lab setup, and `.lake/packages` is a directory junction to that setup's pinned package checkout. This local arrangement requires those external paths to remain available. `-Clean` rebuilds this project's generated artifacts while retaining inherited dependency caches.

For an independent checkout, install the official `elan` toolchain manager and run:

```powershell
.\bootstrap.ps1
```

The bootstrap installs the pinned toolchain, fetches dependencies, retrieves the official Mathlib cache, and invokes clean verification. The current PC's audit is evidence for its pinned local setup; an independent machine must run the bootstrap and audit itself. The shared junction and local compiler are not bundled portable dependencies.

- Lean/Lake: **4.34.1**, Lean commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (release `v4.34.1`).
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` preserve the toolchain and dependency pins.

## Verification evidence

[`verify.ps1`](verify.ps1) builds the default target, independently enumerates imported kernel theorem constants, exports exact public theorem types, and audits every theorem constant, including generated helpers and Unicode names. It checks the compiler version and commit, all dependency revisions and tracked-source cleanliness, and source/configuration hashes. It also checks `OQ7.theorem51` directly against `OQ7.Theorem51Statement` for an arbitrary original `PhysicalParameters` value.

The source gate rejects unfinished proofs and disallowed proof mechanisms. The transitive axiom audit accepts only Lean's standard logical foundations: `propext`, `Classical.choice`, and `Quot.sound`. Added mathematical axioms and native-evaluation axioms are rejected.

| Evidence | Location |
| --- | --- |
| Current verification result, exact theorem names, pins and hashes | [`verification/report.json`](verification/report.json) |
| Clean operation and build output | `verification/clean.log`, [`verification/build.log`](verification/build.log) |
| Independently enumerated kernel declarations | `verification/Inventory.lean`, `verification/inventory.log` |
| Exact exported public theorem types | `verification/Statements.lean`, [`verification/statements.log`](verification/statements.log) |
| Transitive axiom reports and exact final-target check | `verification/Audit.lean`, [`verification/axioms.log`](verification/axioms.log) |
| Independently rechecked original 118 declarations and exact types | `verification/milestones/baseline-118/` |
| Archived successful intermediate audits | `verification/milestones/` |

The baseline and earlier Theorem 4.5 and Section 5 milestones preserve the verification history. Counts and timestamps for the current sources belong in the current report, not in this README. A defined proposition alone is not a proved theorem, and a prior report must be checked against the current source hashes.

## Proof map and implemented adaptations

| Component | Principal modules |
| --- | --- |
| Actual layers, Maxwell fields, scattering, passivity and strict finite-stack gap | `Layers`, `Fields`, `Scattering`, `PhysicalPassivity`, `StrictLoss` |
| Global fields, physical Gram identity and transmission normalization | `PhysicalGlobal`, `PhysicalGram`, `PhysicalIntegrals`, `PhysicalAbsorption` |
| Lemmas 4.1–4.4, finite resource floor and uniform physical Theorem 4.5 | `ModulusComparison`, `PhysicalModulus`, `FourierCap`, `ResourceScalar`, `PhysicalCellBounds`, `ResourceTheorem45` |
| Genuine Maxwell exponential, symmetric core and controlled repeated-product remainder | `PhysicalExponential`, `CoreFactorization`, `PhysicalCellRemainder`, `PhysicalCoreRemainder`, `PhysicalCoreInvariant` |
| Smooth response, invertible matching derivative and exact implicit matching | `MatchingResponse`, `MatchingJacobian`, `MatchingImplicit`, `MatchingTargetImplicit`, `MatchedTransfer` |
| Ordinary dielectric coatings, scalar signs and complete physical accounting | `PhysicalQuarterWave`, `PhysicalCoatings`, `PhysicalCoatedCore`, `PhysicalSignedTransfer` |
| Phase remainder, sharp deficit, all real budgets and final supremum squeeze | `PhaseSmooth`, `SharpDeficit`, `TransferSharpLimit`, `ConstructionBudget`, `PhysicalSequenceSqueeze`, `SharpPhysicalConstruction` |

The formal proof implements the checkpoint's principal adaptations:

- An exact nonnegative scalar tangent remainder supplies the envelope deficit. Half-period convexity and the separate small-mean full-period supporting tangent remain distinct results.
- The modulus comparison uses a finite-interface first-zero argument and a monotone sine Wronskian/ratio, with initial limits derived from the actual fields.
- A positive-part cosine majorant proves the capped Fourier moment, including endpoint masses and arbitrary phases. Open-interval caps remove measure-zero interface artifacts while retaining arbitrary exterior layers.
- Maxwell flux telescoping derives the actual Gram determinant with its transmission factor. Singular-inclusive PSD determinant Minkowski and equal-cell aggregation give a uniform lower bound over changing physical stacks.
- A submultiplicative matrix operator norm, genuine exponential Taylor tails, and direct finite insertion estimates give the repeated-core expansion without matrix logarithms.
- A smooth response extension on all eight real matrix entries enables parameter implicit matching. The physical determinant-one matrices retain exact `T` and `a`; bounded-index quarter-wave coatings realize the matching parameters with zero added loss and all thickness included.
- The unit phase product avoids a principal-argument branch. Its squared distance gives the fourth-order phase penalty. An eventual floor index fits every sufficiently large real budget, proving nonemptiness and the matching supremum limit.

The explicit physical witness is `OQ7.sharp_physical_constructed_sequence`. It proves eventual admissibility, exact `M`, `T`, `a`, the full thickness bound, and the sharp scaled asymmetry limit; `OQ7.theorem51` discharges the final construction hypotheses with that witness.

## Sources and continuation

The supplied paper, [`sources/OQ7_verified_research_note.pdf`](sources/OQ7_verified_research_note.pdf), and [`sources/original-checkpoint.md`](sources/original-checkpoint.md) are unchanged reference material. The original checkpoint records an earlier blocked execution environment and proof plan; its old status is historical. `checkpoint.json` and `proof-progress.json` are continuation ledgers, while the current audit report is the verification authority.

This checkout continues chat `01a12262-a19c-7033-bc2b-9c2cad330224`, whose original project remains at `C:\Users\Daniel\Documents\Codex\2026-10-09\continue-the-oq7-lean-verification-using\outputs\oq7`. Continuation chat `01a12368-a411-7090-b20e-cb00958e2723` works in this project's `outputs\oq7`; the source references were copied unchanged and the original workspace was retained.

Official proof-validation guidance: [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
