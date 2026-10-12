# OQ7 physical Theorem 1.1 — complete kernel proof

The complete declaration is `OQ7Prescribed.theorem11_complete : PhysicalTheorem11Statement` in PrescribedExtinction/PhysicalTheorem11.lean:31. Its first conjunct is the unchanged original existence statement, proved by the preserved `theorem11`. It also proves both exact prescribed-extinction suprema and certifies the original Maxwell and power interpretation. The original existence core alone did not contain the full manuscript conclusion; Claude's independent baseline audit is preserved in verification/claude-independent-audit-5a8350d.md.

| Requested result | Exact declarations | Source |
| --- | --- | --- |
| Universal passivity and Gamma <= 1 | scatteringState_absorption_le_extinction; universal_physical_asymmetry_le_one | UniversalPassivity.lean:117; UniversalPhysicalBounds.lean:38 |
| Outgoing weak uniqueness and converse volume representation | physicalScatteringState_unique_ae; physicalScatteringState_wellposed_ae; scatteringState_converse_material_volume_equation | WeakPhysicalUniqueness.lean:40; WeakPhysicalRepresentation.lean:27 |
| Full optical theorem and X=A+S, with actual all-angle radiation | scatteringState_full_optical_theorem; scatteringState_energy_balance; scatteringState_scattering_is_physical_flux | FullPhysicalOpticalTheorem.lean:28; ArbitraryStateOpticalBalance.lean:39; ScatteringStatePhysicalRadiation.lean:83 |
| Universal strict nonattainment at positive extinction | universal_physical_asymmetry_lt_one | UniversalPhysicalBounds.lean:24 |
| Both full-class suprema and complete theorem | prescribedExtinction_full_supremum; theorem11_complete | FullPrescribedSuprema.lean:80; PhysicalTheorem11.lean:31 |

Every declaration is in namespace OQ7Prescribed. The value sets range over all original admissible bodies and original weak scattering states at the prescribed common extinction, without a volume-equation or constructed-family restriction. Reciprocity proves common extinction for arbitrary opposite-incidence states. Both IsLUB results and nonempty value sets are proved before the sSup equalities.

Weak uniqueness is equality almost everywhere. The canonical exterior fields are proved to represent each weak solution; the original powers are invariant under that equality. The actual full-sphere Poynting integrals are proved genuinely integrable, with an explicit vanishing far-field error, and converge to the original scattering cross section. The original current far field is also identified uniformly over the whole sphere as the canonical electric radiation amplitude. No optical identity, converse, uniqueness, or passivity conclusion is assumed as a structure field or axiom.

The final fresh project build passed 3601 jobs, the exact full theorem declaration/type check, and the exhaustive transitive axiom audit of all 5654 project constants. The only foundations used by the final theorem are propext, Classical.choice and Quot.sound. See verification/report.json and verification/final-complete-theorem.log for the current certificate. Separate obligation exports are in verification/milestones/. The empty-environment kernel replay and frozen review preparation are recorded separately; inspect verification/fresh-kernel-report.json when available.

## Reproduction

Pins: Lean 4.34.1, compiler commit 5045d0056413266e57c625dcd7c365b10e377c52; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. sources/pinned-lake-manifest.json preserves every transitive package revision. Configure build paths in a disposable checkout without changing Lean sources or upgrading pins:

```powershell
./configure.ps1 -PackagesDirectory 'C:/path/to/pinned/.lake/packages'
./verify.ps1 -LeanBin 'C:/path/to/lean-4.34.1-windows/bin' -Clean -BuildThreads 2
./verify-milestones.ps1 -LeanBin 'C:/path/to/lean-4.34.1-windows/bin' -Only obligation-1-universal-passivity,outgoing-weak-uniqueness,obligation-3-full-physical-optics,obligation-4-universal-nonattainment,obligation-5-complete-physical-theorem
./verify-kernel.ps1 -LeanBin 'C:/path/to/lean-4.34.1-windows/bin'
```

configure.py provides the same path setup on other platforms, optionally with --packages-directory. The fresh replay command is `lake env leanchecker --fresh --verbose PrescribedExtinction`; it replays every constant in the aggregate's import closure into an empty environment, using the same Lean kernel implementation. This is distinct from an independently implemented kernel audit.

All original Lean leaf modules from audited commit 5a8350d5408c38e333c9f6b6d8a94816c794120b are byte-preserved; aggregate imports are appended only. Maxwell.lean retains its historical smooth-test annotation correction and stale comments so the guarded source stays unchanged. The manuscript and read-only sources are preserved. The verifier guards these hashes, rejects prohibited proof mechanisms, and checks pinned dependency sources are clean. RESUME.md records session state. verification/INDEPENDENT_REVIEW_PROMPT.md supplies the next independent audit prompt.