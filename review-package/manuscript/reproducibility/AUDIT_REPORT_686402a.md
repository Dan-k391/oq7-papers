# Independent final audit: OQ7 Lean formalization of physical Theorem 1.1

| | |
|---|---|
| Frozen commit | `686402a6c2d63820828729cc7ab02504632e3fe7` (tree `580737ccf6557102d601894145cc0229ae1f83e3`) |
| Previously audited | `5a8350d5408c38e333c9f6b6d8a94816c794120b`, which had open gaps F1–F4 |
| Declaration | `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement` (`PrescribedExtinction/PhysicalTheorem11.lean:31`) |
| Specification | `OQ7_prescribed_extinction_2026-10-11.pdf` (SHA-256 `3d9775d8…6710`), Theorem 1.1 and Lemma 1.2, p. 3 |
| Toolchain | Lean 4.34.1 (`5045d005…`), Mathlib `d13f23b7…`; all transitive pins as verified in the previous audit |

## Verdicts

| Category | Verdict |
|---|---|
| Lean kernel validity | **PASS** |
| Full semantic fidelity to the manuscript's Theorem 1.1 | **PASS** (interpretation scope noted in §3) |
| Maxwell physical correctness within the formal model | **PASS** |
| Completion of F1–F4 | **PASS**, all four closed |
| Exact supremum theorem (both suprema, non-attained) | **PASS** |
| Reproducibility | **PASS**, with two portability defects (R1, R2) that do not affect the result |

No failures were found, so there are no failing file/line items to report.

**Explicit confirmation.** Within the formal model defined in `Basic.lean` and `Maxwell.lean` (re-audited previously, unchanged since), the entire physical Theorem 1.1 is kernel-verified at this commit. That includes:

* the existence statement (3)–(4);
* uniqueness of the physical fields;
* the optical theorem and the equivalence of both forms of Γ;
* universal passivity;
* **both exact suprema** (sup Γ = 1 and sup |A₊−A₋| = E∗ at fixed extinction);
* universal strict non-attainment (Lemma 1.2).

It depends only on `propext`, `Classical.choice` and `Quot.sound`.

---

## 1. Kernel validity: PASS

### Frozen commit reconstruction

* I staged all 172 loose objects plus the pack from the repository's `.git` and reconstructed the repository separately. `git fsck --full` is clean.
* `HEAD` = `686402a6…` (commit message: "Preserve fresh kernel replay and frozen review export evidence"). There are 4 commits since `5a8350d`.
* 37 working-tree files in your folder were hashed (`git hash-object`): all 32 new or changed Lean files, `Maxwell.lean`, `Basic.lean`, `Theorem11.lean`, `lakefile.toml`, `lean-toolchain`. All are **identical to the frozen commit**.

### What changed since `5a8350d`

* 31 new modules were added.
* The only modified library file is the root `PrescribedExtinction.lean`, which gains imports only.
* No previously audited library module is modified or deleted.
* `Maxwell.lean`, `Basic.lean`, `lakefile.toml` and `lean-toolchain` are unchanged. The target definitions are therefore byte-identical to the ones I audited before.

### Build

* `lake build OQ7 PrescribedExtinction`: **3,601 jobs, exit 0**, no `declaration uses 'sorry'` (`logs/build-all.log`).
* All 378 project modules were compiled fresh in a new clone.
* Dependency oleans were reused from my own from-source build of the previous audit, at identical pinned revisions. The two Mathlib modules newly required by this commit were compiled from source here.

### Source scan

All 378 library files contain no `sorry`, `admit`, `axiom` declaration, `opaque`, `unsafe`, `implemented_by`, `@[extern]`, `native_decide`, `ofReduceBool`, `debug.skipKernelTC`, meta-programming, `run_cmd`/`#eval`, or environment manipulation.

The only remaining `ContDiff ℝ ⊤` (analytic) is the historical `AnalyticTestWeakCurl` in `TestRegularity.lean:13`, which is **not** in the final theorem's dependency cone.

### Axioms

* `#print axioms OQ7Prescribed.theorem11_complete` reports `[propext, Classical.choice, Quot.sound]`.
* My own traversal (`experiments/AuditCone2.lean`), which walks types, values, inductives and recursor rules, reaches **61,839 constants** (3,169 of them project constants, in 299 project modules). The only axioms are those three standard ones. There are 0 unsafe constants, and `sorryAx`, `ofReduceBool` and `trustCompiler` are absent.
* A whole-project sweep (`experiments/AuditWholeProject.lean`) covers **5,658 project constants** (49 private). Their union of dependencies reaches only the same three axioms.

### Independent kernel replay

`leanchecker --fresh --verbose PrescribedExtinction.PhysicalTheorem11` replays every constant in the closure (Init, Lean, Std, Batteries, Mathlib, project) into an empty kernel environment. Result: **exit 0** in 10 min 45 s (`logs/leanchecker-fresh-PhysicalTheorem11.log`).

---

## 2. Gaps F1–F4: all closed (PASS)

The final statement (`PhysicalTheorem11.lean:12–29`) contains each item below as an explicit conjunct, not as an unused lemma. Dependency cone (`logs/cone2.log`): the decisive lemmas are all reached, and **30 of the 31 new modules** contribute constants.

* **Reached lemmas**:
  * `physicalScatteringState_unique_ae`
  * `scatteringState_outgoing_volume_representation`
  * `scatteringState_energy_balance`
  * `scatteringState_forward_optical_theorem`
  * `exteriorSphereFlux_tendsto`
  * `scatteringState_absorption_le_extinction`
  * `scatteringState_extinction_reciprocity`
  * `outgoing_weak_source_work_nonneg`
  * `…AsymmetryValues_isLUB`
  * `theorem11`
* **Unused module**: only `DistributionVacuumHelmholtz` contributes no constants. It is an unused helper, and nothing claimed depends on it.

| Gap | Formal content in the statement | Verified meaning |
|---|---|---|
| **F1** universal passivity and suprema | l.25: Γ ≤ 1 for every admissible body and every pair of states. l.15–16: `sSup` of Γ-values = 1; `sSup` of \|A₊−A₋\|-values = E∗. | The class (`PrescribedExtinctionClass.lean:9–27`) is *every* admissible `TwoLayerBody` with *arbitrary* `ScatteringState`s and X₊ = X₋ = E∗. My lemma `auditor_sup_is_lub` derives from the statement alone that Γ ≤ 1 on the class, that Γ > 1−ε is approached for every ε, and that Γ < 1 throughout. Lean's `sSup ∅ = 0` and `sSup(unbounded) = 0` conventions cannot fake "= 1" (checked in the proof). |
| **F2** uniqueness and converse representation | l.18–19: ∃ s ∀ t, E and H agree a.e. For **every** state, `FullPhysicalOpticalStatement` conjuncts 1–2 give E =ᵐ f + E_out[χE] and H =ᵐ H_inc + H_out[χE]. | Uniqueness is a.e., the correct notion for L²_loc fields. The converse representation holds for an *arbitrary* weak radiating solution, not only for constructed ones. It uses strict loss through `admissible`. |
| **F3** optical theorem | Conjuncts 3–7 of `FullPhysicalOpticalStatement` (`FullPhysicalOpticalTheorem.lean:13–26`), for every state. | X = A + S. X = (4π/k)·Im(e_y†F(σe_z)), the manuscript's forward optical theorem. S = ∫_{S²}\|F\|² dσ, with `sphereArea` the Mathlib surface measure of total mass 4π (`SphereMeasure.lean:31`). The Poynting flux r²∫Re(Ē·(H×n)) dσ → S, with the correct normalization for Z₀H units. Uniform far-field bound: \|r e^{−ikr}E_s(rn) − F(n)\| ≤ C/r. l.27–28: Γ = \|S₊−S₋\|/X. l.23: X₊ = X₋ for every pair of states (reciprocity). |
| **F4** universal non-attainment | l.26: X > 0 ⇒ Γ < 1 for every admissible body and every pair of states. l.29: Γ < 1 and \|A₊−A₋\| < E∗ for every member of the class, so neither supremum is attained. | Matches Lemma 1.2 ("X > 0 implies Γ < 1"). |

### Pointwise representatives are canonical

The flux and far-field conjuncts evaluate fields on spheres, which are Lebesgue-null sets. I checked that the evaluated representative is the canonical one:

* outside the body, `scatteringStateRadiatingElectric` is the explicit pointwise dyadic-Green integral `∫ classicalDyadic k (x−y) p(y) dy` (`ExteriorOutgoing.lean:73`), on `‖x‖ > R+1` (`OutgoingSourceFields.lean:77`);
* the magnetic field is a pointwise convolution;
* both are proved a.e. equal to the weak solution.

So these statements are about the genuine continuous radiating field, not an arbitrary a.e. version.

---

## 3. Semantic fidelity: PASS

### Mapping from Theorem 1.1 to `PhysicalTheorem11Statement`

| Manuscript Theorem 1.1 / Lemma 1.2 | Statement | Status |
|---|---|---|
| ∀ k, P, Q, E∗, ϵ: ∃ two-layer body with (3) such that X₊ = X₋ = E∗ and 1−ϵ < Γ < 1 | conjunct 1 = the unchanged `Theorem11Statement` (re-audited previously) | ✓ |
| "the pair (1)", i.e. the unique physical outgoing fields | l.18–19 (existence + a.e. uniqueness) and the converse representation | ✓ (was F2) |
| sup_{X=E∗} Γ = 1 in this class | l.15 | ✓ (was F1) |
| sup_{X=E∗} \|A₊−A₋\| = E∗ | l.16 | ✓ (was F1) |
| Γ = \|A₊−A₋\|/X = \|S₊−S₋\|/X, X = A± + S± | l.27–28; energy balance for every state | ✓ (was F3) |
| X₊ = X₋ (reciprocity) | l.23 | ✓ |
| Lemma 1.2: X > 0 ⇒ Γ < 1 | l.26 | ✓ (was F4) |
| Forward optical theorem X = (4π/k)·Im(e_y†F(±e_z)) | optical conjunct 4 | ✓ |

### Adversarial checks

1. **Test-function space.** The final theorem uses only `HasWeakCurl` with `ContDiff ℝ (⊤ : ℕ∞)`, i.e. C^∞_c. I re-ran my previous experiments against this build (`logs/regression-experiments.log`), all with standard axioms only:
   * the old analytic class is still vacuous (`auditor_old_weakCurl_vacuous`);
   * the corrected class still rejects "curl 0 = e_x" (`auditor_new_weakCurl_nonvacuous`);
   * `AnalyticTestWeakCurl` is outside the cone.
2. **Improper or default-zero integrals.** Re-verified for every `ScatteringState`: absorption and all four weak-Maxwell integrands are genuinely integrable (`auditor_absorption_integrable`, `auditor_weakMaxwell_integrands`).
3. **Division by zero in Γ.** The universal Γ ≤ 1 clause (l.25) is proved via the X = 0 branch (`UniversalPhysicalBounds.lean:42–43`), where Lean sets x/0 = 0. The repo never proves X > 0 universally, but the manuscript asserts it ("X = X₊ = X₋ > 0", p. 3). **I proved it** (`auditor_extinction_pos`, `experiments/Audit2.lean`): for every admissible body and every state, X > 0. The argument: X = 0 ⇒ A = 0 ⇒ E = 0 a.e. in the body (strict loss) ⇒ P = 0 ⇒ E = f a.e. (converse representation), contradicting \|f\| = 1 on a set of positive measure. Hence the X = 0 branch is vacuous, and Γ < 1 holds for every admissible body with no hypothesis (`auditor_universal_gamma_lt_one`). This closes a small gap in the repo's statement rather than revealing a defect.
4. **Vacuity.** `ScatteringState` is inhabited for every admissible body (l.18). The universal clauses therefore quantify over a non-empty class, and the supremum sets are proved non-empty.
5. **Normalizations.** The base definitions are unchanged (incident amplitude, Z₀H, Silver–Müller sign for e^{−iωt}, X, A, Γ). The new ones were checked:
   * flux is Re(E×H̄)·n in Z₀H units, i.e. cross-section normalization;
   * the far-field factor is k²/4π;
   * the sphere mass is 4π;
   * the forward direction is σe_z.

### Interpretation scope (not failures)

* **"In this class"** is formalized as the manuscript's own geometry: the slab D_R = S_R × (0, h+d), axis-aligned and origin-anchored, illuminated along its normal by e_y-polarized ±e_z plane waves. The admissible tensors are arbitrary. A broader reading (rotated or translated bodies, other shapes) is not covered. Mathematically the upper bound Γ ≤ 1 still holds for those by passivity, but that is not formalized.
* The formal class also admits equal absorber and plate tensors. This is harmless: the lower-bound witnesses have distinct layers, and the upper bound holds on the larger class.
* The theorem is single-frequency. The causality and dispersion remarks (§5.3) and the bounded-resource asymptotics (§6) are outside Theorem 1.1 and were not audited.

---

## 4. Maxwell physical correctness within the formal model: PASS

* The weak Maxwell equations (C^∞_c tests, μ = I), local L², and the uniform Silver–Müller condition are unchanged from the previous audit, where they were verified, and are re-confirmed non-vacuous here.
* Uniqueness and the converse representation hold for arbitrary weak radiating solutions.
* Energy balance, flux convergence, far-field identification and reciprocity hold for **every** state, not only the constructed witnesses.

---

## 5. Reproducibility: PASS (with portability defects)

* The frozen commit hash, fsck, working-tree identity (37 files) and byte-preservation of all `5a8350d` modules are verified.
* The repo's claims of 3,601 build jobs and fresh `leanchecker` success are reproduced independently. Its 5,654-constant count differs slightly from my 5,658 because of how generated declarations are counted; both find the same three axioms.
* **R1**: `lake-manifest.json` is still git-ignored. The pins are tracked in `sources/pinned-lake-manifest.json` and match Mathlib's manifest.
* **R2**: `lakefile.toml:3` still points `packagesDir` at an absolute Windows path. On POSIX this breaks `lake env`; I worked around it with a symlink and an explicit `LEAN_PATH` (`env.sh`).
* The repo's PowerShell verifiers (`verify*.ps1`) were inspected but not run. Their substantive checks were reproduced.

### Reproduction

```bash
git checkout 686402a6c2d63820828729cc7ab02504632e3fe7
lake build OQ7 PrescribedExtinction                     # 3601 jobs
source env.sh                                           # LEAN_PATH workaround (R2)
lean experiments/Audit2.lean                            # A0–A3: axioms, sup⇔lub, X>0, universal Γ<1
lean experiments/AuditCone2.lean                        # dependency cone of theorem11_complete
lean experiments/AuditWholeProject.lean                 # all 5,658 project constants
lean <prev>/AuditExperiments.lean                       # regression: test-space + integrability
leanchecker --fresh --verbose PrescribedExtinction.PhysicalTheorem11
```

---

## 6. What this does and does not establish

* **Established.** A machine-checked proof, relative to Lean's kernel and Mathlib's standard definitions, that the formal statement holds. On my review, that statement faithfully encodes the manuscript's Theorem 1.1 and Lemma 1.2 for linear, local, reciprocal, nonmagnetic dielectric two-layer slabs at one frequency.
* **Not established by Lean.**
  * Scientific novelty or priority.
  * Experimental or engineering realizability, e.g. finite bandwidth, real-material dispersion, or fabrication of the unbounded aperture and thickness sequences.
  * That this is *the* resolution of OQ7 under every interpretation. OQ7 itself fixes no normalization or resource class; the manuscript's §1 says so.
  * The manuscript's §6 results.
* **Trust base.**
  * The Lean 4.34.1 release binary.
  * `leanchecker`, which uses the same kernel implementation; no independent kernel (e.g. lean4lean) was used.
  * The standard meaning of Mathlib's definitions.
  * My reading of the manuscript.
  * For dependencies, my earlier from-source Mathlib build at identical pins. Everything was then re-checked by the fresh kernel replay.
