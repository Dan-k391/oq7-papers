# OQ7 physical prescribed extinction — verification in progress

The preserved existence declaration is `OQ7Prescribed.theorem11 : Theorem11Statement`. Claude's independent audit of commit `5a8350d5408c38e333c9f6b6d8a94816c794120b` confirms its kernel validity and identifies obligations omitted from the earlier completion claim. The audit is preserved in verification/claude-independent-audit-5a8350d.md. Full physical verification remains pending.

The continuation proves universal passivity directly for every original outgoing weak Maxwell state: `scatteringState_absorption_le_extinction`. Admissibility gives nonnegative absorption; positive extinction gives strictly positive absorption. The proof derives compact weak integration by parts through actual Fourier curl symbols and Plancherel, then a weak cutoff Poynting identity and the full uniform Silver–Muller radiation condition. It assumes no volume equation or physical power identity.

`prescribedExtinction_full_supremum` proves both exact sharp values, `sSup prescribedExtinctionAsymmetryValues = 1` and `sSup prescribedExtinctionDifferenceValues = target`, and strict nonattainment for every member. `PrescribedExtinctionPair` ranges over all original admissible bodies and original weak states with both extinctions equal to the prescribed positive target. It is not restricted to the constructed family or volume-integral states. The lower bound uses the preserved existence proof; the upper bound uses universal weak passivity and strict material loss.

Outgoing weak-state uniqueness and converse volume representation are now proved. Remaining requested physical obligations are arbitrary-state X=A+S with S identified as actual all-angle outgoing radiation, and reciprocity/bounds for arbitrary opposite-incidence states without an explicit common-extinction hypothesis. A combined final declaration and frozen review repository are due after these are proved. No completion should be inferred from the existence-core certificate alone.

## Reproduction and evidence

Pins: Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Configure without upgrading the pinned dependencies:

```powershell
./configure.ps1
./verify.ps1 -LeanBin 'C:/path/to/lean-4.34.1-windows/bin' -Clean -BuildThreads 2
./verify-milestones.ps1 -LeanBin 'C:/path/to/lean-4.34.1-windows/bin' -Only universal-weak-passivity,full-prescribed-suprema
```

To reuse pinned packages, pass `-PackagesDirectory 'C:/path/to/.lake/packages'` to configure.ps1. `verification/report.json` records the exact current scope, source hashes, pinned dependency revisions and exhaustive transitive axiom audit. `verification/clean-build.log`, `verification/axioms.log`, and the selected milestone directories preserve build and declaration evidence. Standard foundations allowed are only `propext`, `Classical.choice`, and `Quot.sound`.

Every original Lean leaf module from the audited commit is byte-preserved; the aggregate imports are only appended. Maxwell.lean retains the historical documented correction to all C-infinity compact tests and its exact guarded source hash. The manuscript and synced reference sources are unchanged. `RESUME.md` records the next analytic steps and safe continuation procedure.
The next continuation adds `scatteringState_outgoing_volume_representation`, `scatteringState_converse_material_volume_equation`, `physicalScatteringState_unique_ae`, and `physicalScatteringState_wellposed_ae`. These apply to every original weak scattering state. A free outgoing weak pair is eliminated by the proved weighted vacuum energy and Lorentz identities against every compact smooth current. This checkpoint passed a fresh 3593-job clean build and exhaustive transitive audit of all 5603 project constants. Check the current report for the certified scope.
