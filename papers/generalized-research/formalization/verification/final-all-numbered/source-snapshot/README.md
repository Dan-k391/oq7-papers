# Generalized-research formalization

This is a separate revision. The prescribed-extinction project and historical
proof archives are dependencies; their sources and pins are unchanged.

The target is the dated manuscript
`../manuscript/OQ7_generalized_research_2026-10-10.pdf`. The verification report
records its SHA-256, the arXiv source hash, every new proof-source hash, all
preserved dependency-source hashes, and the exact compiler/package revisions.
The report is evidence for those exact versions, not for future edits.

## Reproduce

Use Lean `leanprover/lean4:v4.34.1` and the prescribed-extinction project's
Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. Restore the pinned
dependencies and build the unchanged prescribed-extinction libraries first.
Then, from this directory, run:

```text
python verify.py --lean-bin /absolute/path/to/the/pinned/toolchain/bin --output-dir verification/new-run
```

Python 3.10 or later is sufficient; the verifier uses the standard library.
It compiles every new module in dependency order, compiles the aggregate,
prints the exact type and transitive axioms of every theorem in the new
namespace (including generated theorem helpers), and runs
`leanchecker --fresh --verbose GeneralizedResearch`. It rejects `sorry`,
`admit`, `native_decide`, new axiom declarations, and every transitive axiom
except `propext`, `Classical.choice`, and `Quot.sound`. It also rejects source,
import-graph, package-pin or tracked dependency changes during verification.
The required public-root manifest also binds 439 explicitly named theorem roots
to exact printed kernel types, while the exhaustive audit covers all 1,644
theorem declarations, including generated helpers.

`--elaborate-only` is development mode and explicitly does not certify a fresh
kernel replay. A fresh replay uses Lean's kernel again; it is not a separate
kernel implementation or human peer review. Only a completed report with
`status: fresh-kernel-passed` records a successful final run.

For the newest 75-module run, inspect `verification/final-all-numbered/report.json`.
An earlier 71-module development run completed elaboration and its declaration
census but was intentionally stopped during fresh replay when this complete
75-module graph was ready. Its partial report, logs and exact source snapshot
are preserved in ignored `.local/verification-superseded/` storage. It is not
a successful fresh-verification record and is not publication evidence.
The earlier `verification/checkpoint-main-claims/` record and its exact source
snapshot remain preserved; that earlier checkpoint did not include the beam
corollary, literal small-dimension wrapper, or piecewise envelope continuity.

Expected-failure controls are independent of the successful proof project and
can be rerun in an isolated scratch directory:

```text
python negative_controls.py --project /absolute/path/to/this/project --scratch /absolute/path/to/ignored/scratch --lean-bin /absolute/path/to/the/pinned/toolchain/bin
```

Their report records which guards rejected deliberately false, incomplete or
axiom-using fixtures. The production sources are never modified by these
controls. A control's intended rejection is not a successful theorem proof.

## Statement correspondence

All names below have prefix `GeneralizedResearch`.

| Dated manuscript statement | Formal source and principal declarations |
|---|---|
| Propositions 2.1–2.2, closed scalar feasible set and both sharp branches | `ScalarBenchmark.feasibility_iff`, `sharp_ceiling`, `optimizer_attains`; endpoint and transition theorems in the same module. All original Proposition 2.1 clauses, including prescribed-entry arg/cos Eq6 and the degenerate determinant criterion, are combined in `ScalarPhaseFeasibility.proposition21` |
| Lemmas 4.1–4.4 and Theorem 4.5, broad selected-interval resource floor | `HelmholtzProfile.Profile.modulus_comparison`, `cell_det_lower`, `theorem45_finite`, `theorem45_scattering_floor`, `theorem45_uniform_asymptotic`, `theorem45_sequence_lowerlimit`; literal unit-incidence cell Grams/actual transmitted power and arbitrary disjoint-cell aggregation in `HelmholtzProfile.Profile.lemma43`, `HelmholtzProfile.Profile.unitCellGram_congruence`, `HelmholtzProfile.Profile.unitCellGram_normalized_det`, `HelmholtzProfile.Profile.disjoint_resource_cells`; existing capped-Fourier and scalar-convexity proofs are imported unchanged |
| Theorem 5.1, actual scalar finite-layer exact-target asymptotic | `sharp_exact_target_thickness`, a wrapper of the unchanged `OQ7.theorem51` |
| Corollary 5.2, minimum physical thickness | `corollary52`, `corollary52_original_ratio`, `minimumThickness_tendsto_atTop` |
| Proposition 6.1 and Theorem 6.2, actual Hilbert reciprocity/passivity/equality and sharpness | `ChannelReciprocity`, `ChannelPassivity`, `ChannelEquality`, `ChannelParabola`; finite matrix powers are also proved in `ChannelPowers` |
| Theorem 6.3, fixed-extinction scalar envelope and golden-ratio contrast | `ScalarContrast.fixed_extinction_sharp`, `fixed_ceiling_formula`, `theorem63`, `golden_attained`; all Eq52 equality matrices, every real phase and port interchange in `GoldenClassification.theorem63`, `equality_family_iff`, `family_attains`; `ScalarPhase` and `ScalarPhysicalSharpness.physical_golden_sequence` prove the actual dielectric sequence with its counted phase slab |
| Theorem 6.4, actual normal-incidence anisotropic two-layer realization and limits | `PlanarFourPort`, `PlanarPlateBridge`, `PlanarRealization`, `DiagonalAbsorber`, `PlanarSharpness.fixed_extinction_supremum`, `relative_supremum`, `positive_budget_zero_absorption` |
| Corollary 6.5, actual finite-power planar beams under fixed material caps | `PhysicalBeamCorollary.corollary65`, `realizes`, `radiation`, `actual_reference`, `true_time_reverse`; `PhysicalBeamUpper.corollary65_sSup`, `relative_one`; `BoundaryFlux.net_physical_flux`, `total_boundary_integrals_ae`; exact physical Fourier convention, regional Maxwell fields, all interfaces and transverse L² are proved in the imported beam modules |
| Theorem 7.1, full prescribed-overlap channel maximum | `theorem71`, `theorem71_clm_reference`; exact branch formula and unique parameter in `CanonicalEnvelope` and `MiddleParameters`; equality conditions and necessary branch thresholds in `MiddleCertificate`, `CanonicalMiddle`, `TransitionConditions`; literal n≤3 same-Hilbert witnesses in `SmallAttainment.theorem71_dimension` and full piecewise continuity in `EnvelopeContinuity.envelope_continuous` |

The broader resource model stores literal continuous electric/magnetic
fundamental fields, their Maxwell equations off a finite interface set, the
initial identity matrix, and locally integrable nonnegative loss. It imposes
no lower bound on real permittivity. Unimodularity, flux/Gram identities,
nonzero transmission, scattering passivity and every resource floor are
derived. `ProfileExamples` gives explicit zero- and negative-permittivity
Maxwell solutions and embeds the unchanged finite-layer model exactly.

The overlap upper bound covers arbitrary Hilbert dimension, an actual
conjugation, actual reciprocal contractions, arbitrary reciprocal lossless
references, and arbitrary input phase. It derives the canonical frame and
real compression from those operators. Sharpness uses actual complex
matrices, then `FiniteHilbertBridge` proves their equivalence to the identical
Hilbert observables used by the upper statement. A reciprocal bounded
reference with `S₀.adjoint.comp S₀ = id` is proved onto, rather than assumed so.

The planar construction includes actual differential fields, constitutive
currents, electric/magnetic interface continuity, and external incoming and
outgoing boundary states for every four-port input. Its reference is proved
to be vacuum propagation across the complete two-layer length. The varying
loss/thickness slab limit is proved from the exact transfer coefficients;
a fixed-index thick-slab limit is not substituted for it.

The finite-power construction uses the explicit normalized uniform disk
aperture. Its actual oblique Maxwell transfer yields reciprocal passive
scattering and continuous dependence on transverse physical wave number and
the plate parameter. Exact target extinction follows from a proved uniform
narrow-disk limit and the intermediate value theorem. Every material and
exterior field is a physical angular integral with the unitary convention
`(2π)⁻¹∫ exp(i κ·x) f(κ) dκ`. Parseval is proved after the required two-dimensional
dilation of Mathlib's standard Fourier convention. Physical electric and
magnetic fields carry the explicit √2 factor, so their time-averaged
`½ Re(E†H)` flux equals the channel power. The total-boundary flux proof also
cancels the incoming/outgoing interference terms and includes the right-port
orientation. Time reversal explicitly reverses transverse wave number.

## Outstanding scope

The source-bound claim inventory is
`verification/final-all-numbered/claim-coverage.json`. Read each claim's explicit
scope and remaining obligations; theorem counts do not mean that every sentence
of the manuscript has been formalized. In particular, the strictness of the
finite-cell resource-floor inequalities (Remark 4.6), the separate fixed-(T,a)
scalar optimizer and singular-spectrum classification following Proposition
2.2, and some unnumbered endpoint/example/dispersion claims remain tracked.
The beam proof establishes classical Maxwell equations in each homogeneous
region, matched interfaces and radiation expansions. It does not claim a
separate global distributional gluing theorem or every arbitrary L² aperture.

This project makes no compact-body three-dimensional cross-section,
finite-bandwidth, priority/novelty, or human-review claim. The manuscript's
ordinary proofs, numerical experiments, formal proofs, and publication
metadata remain separate evidence categories.

## Final all-numbered-statement verification

All 75 ingredient modules and their aggregate passed compilation, the exhaustive 1,644-theorem type/axiom audit, 439 exact public-root guards and fresh kernel replay. All 15 original numbered statements are complete in the final correspondence ledger, including the full prescribed-entry phase and degenerate clauses of Proposition 2.1 (`ScalarPhaseFeasibility.proposition21`) and every Eq. (52) equality matrix in Theorem 6.3 (`GoldenClassification.theorem63`, `equality_family_iff`, `family_attains`). Six unchanged imported OQ7 correspondence roots have a separate exact type/axiom record. All 13 isolated rejection/positive controls passed. The final report and claim ledger are under `verification/final-all-numbered/`.

Remark 4.6 concerns strictness of the finite-cell resource-floor inequalities and remains separate from the already-proved strict finite-stack thickness deficit. The unnumbered full fixed-(T,a) optimizer phase and singular-spectrum classification remains open; the golden-ratio equality family is fully proved. The unfinished 71-module replay was superseded before success and preserved in ignored `.local/verification-superseded/`; it is not publication evidence.
