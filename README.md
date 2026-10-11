# OQ7 physical prescribed extinction — kernel verified

The exact physical Theorem 1.1 is proved by `OQ7Prescribed.theorem11 : OQ7Prescribed.Theorem11Statement` in [Theorem11.lean](PrescribedExtinction/Theorem11.lean). The fresh clean build and exhaustive transitive axiom audit passed on 2026-10-11. The final theorem depends only on Lean's standard foundations `propext`, `Classical.choice`, and `Quot.sound`.

For every positive frequency, real material cap P greater than one, positive loss cap Q, positive prescribed extinction, and epsilon between zero and one, the proof constructs a finite actual two-layer body with strictly admissible tensors and both original incident-direction scattering states. Both physical extinction cross sections equal the target exactly, and the original absorption asymmetry is strictly between one minus epsilon and one. The states satisfy both physical weak Maxwell curls, local square integrability, and the full uniform Silver–Muller condition over all directions. The final theorem has no additional physical assumptions.

## Verified dependency chain

| Milestone | Main proof modules |
| --- | --- |
| Physical static operator, including Newton contact and Fourier identification | NewtonContact, NewtonTransform, NewtonStaticIdentification |
| Actual bounded outgoing operator and global radiating Maxwell fields | OutgoingVolumeIdentification, CompactOutgoingIdentification, OutgoingSourceFields, VolumeScatteringBridge |
| Scattering existence, dissipativity, original full-angular optical balance, and reciprocity | ScatteringExistence, OutgoingDissipativity, PhysicalOpticalBalance, ExtinctionReciprocity |
| Uniform aperture localization for actual normalized currents and original physical powers | UniformBodyResponse, UniformPhysicalPowers, UniformPhysicalAsymmetry |
| Actual planar design, first finite-body bracket, positive isotropic loss, exact tuning, and admissible final witness | PlanarPrescribedDesign, PhysicalRankOneExtinctionBracket, PhysicalCompactLossBracket, PhysicalIsotropicPrescribedExtinction, Theorem11 |

The added generic bounded Woodbury and compact parameter-neighborhood lemmas are proved in BoundedWoodbury and CompactParameterNeighborhood. Strict positive isotropic loss gives positive physical absorption in both directions, which yields strict nonattainment of asymmetry one. Continuity and the intermediate value theorem tune the final angle to the prescribed extinction after adding this loss.

## Reproducible certificate

- [verification/report.json](verification/report.json): `status: VERIFIED`, `theorem11Verified: true`, final theorem declaration, clean-build/source-hash equality, pinned dependency revisions, and no remaining Theorem 1.1 obligations.
- [verification/final-theorem.log](verification/final-theorem.log): exact theorem type, transitive axioms, and verification that the declaration is a kernel theorem with exactly Theorem11Statement.
- [verification/clean-build.log](verification/clean-build.log): successful fresh project build, 3568 jobs.
- [verification/axioms.log](verification/axioms.log) and [verification/inventory.log](verification/inventory.log): exhaustive audit of all 5402 public, private, and generated project constants selected by the project namespace inventory.
- [verification/milestones/physical-theorem11/axioms.log](verification/milestones/physical-theorem11/axioms.log): independently exported final milestone statements and transitive axioms.
- [verification/physical-theorem11-clean-verification.log](verification/physical-theorem11-clean-verification.log): successful final verifier result.

Pins: Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The canonical transitive manifest is [sources/pinned-lake-manifest.json](sources/pinned-lake-manifest.json). Configure without upgrading dependencies, then verify:

```powershell
./configure.ps1
./verify.ps1 -LeanBin 'C:/path/to/lean-4.34.1-windows/bin' -Clean
./verify-milestones.ps1 -LeanBin 'C:/path/to/lean-4.34.1-windows/bin' -Only physical-theorem11
```

To reuse existing pinned packages, pass `-PackagesDirectory 'C:/path/to/.lake/packages'` to configure.ps1. The verifier checks every tracked dependency is clean at its pinned revision, bans prohibited proof mechanisms, inventories kernel theorem declarations, checks all transitive project axioms, guards the physical target's exact source, and requires a clean build of identical Lean sources before issuing VERIFIED.

## Physical statement and preservation

The whole Theorem11Statement body, its parameters, finite geometry, tensor caps, original cross sections, and full outgoing quantifiers are preserved. The sole historical target-source edit explicitly strengthens compact curl testing from analytic tests to all C-infinity tests with `ContDiff ℝ (⊤ : ℕ∞)`. The exact original source is archived in [verification/physical-target-before-test-correction.txt](verification/physical-target-before-test-correction.txt), and the verifier permits precisely that annotation replacement. TestRegularity proves the corrected condition implies the original one. Current target SHA256: `A9950F0F1C9EA4A20FF2C480A71CC4FABDC4AB84F8173851C37A4BD56E0D231B`.

Maxwell.lean deliberately retains its historical "unproved" comments so its guarded source remains unchanged. Theorem11Statement remains a proposition definition; Theorem11.lean now provides its actual proof declaration. Historical milestone documents and old PARTIAL logs describe earlier commits; the current certificate is verification/report.json.

The manuscript and all read-only sources are preserved. The original OQ7 library's scalar one-dimensional Theorem 5.1 is separate from this physical three-dimensional theorem. Additional converse outgoing-volume representation and uniqueness of arbitrary outgoing Maxwell states are not proved here and are not dependencies of this existential final statement.
