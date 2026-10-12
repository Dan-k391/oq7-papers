# Complete physical Theorem 1.1

Exact proof: `OQ7Prescribed.theorem11_complete : PhysicalTheorem11Statement`,
PrescribedExtinction/PhysicalTheorem11.lean:31. Its first conjunct preserves
Theorem11Statement and the original theorem11 proof. The additional conjuncts
contain both exact supremum values and the full physical certificates.

| Obligation | Result | Exact declarations and locations | Separate certificate |
| --- | --- | --- | --- |
| 1. Universal passivity and Gamma <= 1 | Kernel verified | scatteringState_absorption_le_extinction, UniversalPassivity.lean:117; universal_physical_asymmetry_le_one, UniversalPhysicalBounds.lean:38 | milestones/obligation-1-universal-passivity/axioms.log |
| 2. Outgoing weak uniqueness and converse | Kernel verified | physicalScatteringState_unique_ae, WeakPhysicalUniqueness.lean:40; scatteringState_converse_material_volume_equation, WeakPhysicalRepresentation.lean:27 | milestones/outgoing-weak-uniqueness/axioms.log |
| 3. Full optical theorem and physical X=A+S | Kernel verified | scatteringState_full_optical_theorem, FullPhysicalOpticalTheorem.lean:28; scatteringState_energy_balance, ArbitraryStateOpticalBalance.lean:39; scatteringState_scattering_is_physical_flux, ScatteringStatePhysicalRadiation.lean:83 | milestones/obligation-3-full-physical-optics/axioms.log |
| 4. Universal strict nonattainment | Kernel verified | universal_physical_asymmetry_lt_one, UniversalPhysicalBounds.lean:24 | milestones/obligation-4-universal-nonattainment/axioms.log |
| 5. Both exact suprema and complete theorem | Kernel verified | prescribedExtinction_full_supremum, FullPrescribedSuprema.lean:80; theorem11_complete, PhysicalTheorem11.lean:31 | milestones/obligation-5-complete-physical-theorem/axioms.log |

All declarations have namespace OQ7Prescribed; source paths above are relative
to PrescribedExtinction/. Each certificate directory also contains build.log
and Audit.lean with exact type exports. The common fresh clean build completed
3601 jobs; its log is clean-build.log. The exhaustive all-project transitive
audit checked 5654 public, private, and generated constants; see axioms.log,
inventory.log and report.json. The complete declaration/kind/type check is
final-complete-theorem.log. Only propext, Classical.choice and Quot.sound are
used by the final theorem; no prohibited proof mechanism or custom physical
axiom is used.

The complete physical aggregate import closure was additionally replayed into
an empty kernel environment with `leanchecker --fresh --verbose
PrescribedExtinction`; see leanchecker-fresh.log and fresh-kernel-report.json.
This uses the same Lean kernel implementation and is not an independently
implemented kernel audit. All 378 certified Lean source hashes matched before
and after that replay.

Weak uniqueness is equality almost everywhere. The canonical exterior
representative is proved to represent every original weak solution, and its
genuine full-sphere Poynting flux converges to the original all-angle S. The
original far field is also identified uniformly as its actual electric
radiation amplitude. Reciprocity proves common extinction for arbitrary
opposite-incidence states. The supremum sets cover the entire original
admissible fixed-extinction class, and their nonemptiness and IsLUB properties
are established.

No mathematical obligations remain. All audited original Lean modules from
5a8350d5408c38e333c9f6b6d8a94816c794120b are byte-preserved. Verified milestone
commits include 0708cabce1d0716c9ff7092d7dc1a676f44f485d (passivity/full-class
suprema), a31c6b28c033d4ebcba7fdc066ca07c4052bee6d (weak well-posedness and
converse), and 7acd1e1a79a7ea03fc8a645f02704aad2db89df6 (complete physical
theorem). The accompanying frozen manifest records the final commit with
fresh replay evidence, Git-bundle verification and source-archive hashes.
Independent semantic review of that frozen commit remains available through
INDEPENDENT_REVIEW_PROMPT.md.
