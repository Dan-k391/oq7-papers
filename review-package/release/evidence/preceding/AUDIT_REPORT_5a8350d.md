# Independent audit: OQ7 Lean formalization of physical Theorem 1.1

| | |
|---|---|
| Repository | `oq7-prescribed-extinction` (read-only; isolated clone used) |
| Audited commit | `5a8350d5408c38e333c9f6b6d8a94816c794120b` (tree `a1b03d72e958851f2418f97a6b5c40c0689e305c`) |
| Specification | `sources/OQ7_prescribed_extinction_2026-10-11.pdf`, SHA-256 `3d9775d849234e828370d7c96d8bdcdd574beb6831a7906ea6b7706579868710`, Theorem 1.1 (p. 3) |
| Claimed declaration | `OQ7Prescribed.theorem11 : OQ7Prescribed.Theorem11Statement` (`PrescribedExtinction/Theorem11.lean:11`) |
| Audit date | 2026-10-11/12 (America/New_York) |

## Verdicts

| Category | Verdict | One-line reason |
|---|---|---|
| 1. Kernel validity | **PASS** | Rebuilt from source; `theorem11` has exactly type `Theorem11Statement`. Its transitive axioms are only `propext`, `Classical.choice` and `Quot.sound`. A fresh `leanchecker` kernel replay of the whole closure succeeded. |
| 2. Semantic fidelity | **FAIL** (the existence core passes) | Hypotheses (3) and conclusion (4) are expressed faithfully. Theorem 1.1's own concluding clause, "sup_{X=E∗} Γ = 1 in this class, and sup_{X=E∗} \|A₊−A₋\| = E∗", is absent (F1). The statement also quantifies existentially over solutions, so it only refers to "the" physical solution if uniqueness holds (F2). |
| 3. Mathematical completeness | **FAIL** (incomplete; nothing shown false) | Results the manuscript's claim needs are not proved in Lean: passivity Γ ≤ 1 for every admissible body (F1), uniqueness or converse representation (F2), and the optical-theorem / X = A+S identification (F3). The universal Lemma 1.2 is also missing (F4). All are classical and believed true, and none is needed for the existential Lean statement itself. |

"FAIL" in category 3 means *not established*. I found no evidence that any part of the manuscript's Theorem 1.1 is false.

---

## 1. Kernel validity: PASS

### Toolchain and dependency identities (independently verified)

* **Lean**: release tarball `lean-4.34.1-linux.tar.zst` from GitHub releases. SHA-256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.
  * `lean --version` reports `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.
  * `Lean.githash` evaluates to `5045d0056413266e57c625dcd7c365b10e377c52`.
  * `git ls-remote` on `leanprover/lean4` shows `refs/tags/v4.34.1` → `5045d005…`.
* **Mathlib**: `git ls-remote` shows `refs/tags/v4.34.1` and `refs/heads/stable` → `d13f23b723b8a846827a245b89c10fc7d3f11612`. That commit's `lean-toolchain` is `leanprover/lean4:v4.34.1` (commit dated 2026-09-24, "chore: bump toolchain to v4.34.1").
* **Transitive dependencies**: resolved by Lake from scratch, then compared three ways:
  * against Mathlib's own `lake-manifest.json` at `d13f23b`;
  * against the repo's `sources/pinned-lake-manifest.json`;
  * against the user's untracked working-tree `lake-manifest.json`.

  All three agree on every revision, and every checkout was clean (`git status --porcelain` empty):

| package | revision |
|---|---|
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| batteries | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` |
| Qq | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` |
| aesop | `355695d523e41d0554926416cba2a2b3544fbbc9` |
| proofwidgets | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` |
| importGraph | `e928b72544873815af278d38681b31c0293588e3` |
| LeanSearchClient | `ddf04cf3949fa556442341e87d47f9f6e6074707` |
| plausible | `118aa17ee84656b8bd727fef7c458ee8c833385c` |
| Cli | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` |

### From-source build

* No prebuilt artifacts were used. Mathlib's post-update `cache get` failed. All six optional Reservoir "barrel" downloads returned 404, and Lake logged "building from source". No `.barrel` or `.ltar` file exists. The only oleans present before the build were the 19 Lake had just compiled locally for Mathlib's cache tool.
* `lake build PrescribedExtinction.Theorem11`: **3494 jobs, exit 0, 96 min wall time** on 2 cores. This includes 2837 Mathlib modules and 274 project modules.
* `lake build OQ7 PrescribedExtinction` (all default targets): **3568 jobs, exit 0**.
* Neither build log contains `declaration uses 'sorry'`. Only linter and deprecation warnings appear.

### Source scan

All 347 library files (77 in `OQ7/`, 268 in `PrescribedExtinction/`, plus the two root files) contain no `sorry`, `admit`, `axiom` declaration, `opaque`, `unsafe`, `implemented_by`, `@[extern]`, `native_decide`, `ofReduceBool`, `debug.skipKernelTC`, `macro`/`elab`/`syntax`, `initialize`, `run_cmd`/`#eval`, environment manipulation, or `import Lean`. The one textual hit for "axiom" is a comment (`OQ7/Envelope.lean:135`).

Options used are `backward.isDefEq.respectTransparency false` (179 occurrences) and `maxHeartbeats`/`maxRecDepth`. These affect elaboration only, not the kernel.

### Exact declaration and axioms

`experiments/AuditExperiments.lean:18–20` reports:

```
OQ7Prescribed.theorem11 : OQ7Prescribed.Theorem11Statement
'OQ7Prescribed.theorem11' depends on axioms: [propext, Classical.choice, Quot.sound]
```

My own traversal (`experiments/AuditTraversal.lean`, which walks the type and value of every reachable constant, plus inductives, constructors and recursor rules) found:

* **61,339 reachable constants**: 47,649 theorems, 11,191 defs, 1,034 inductives, 1,130 constructors, 280 recursors, 48 opaques, 4 quot, 3 axioms.
* **Axioms reached**: `propext`, `Classical.choice`, `Quot.sound`. These are Lean's standard foundations: propositional extensionality, global choice, and quotient soundness. **No additional axioms.**
* `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`: absent. No `unsafe` constants are reached.
* The 48 opaques are Mathlib `irreducible_def` wrappers (`…wrapped._@…`) plus `Lean.opaqueId` and `String.Internal.append`. Opaque values are kernel-checked.
* **2,771 project constants** are reached, across 256 modules: 4 private and 1,066 auxiliary or generated (`match_`, `proof_`, `eq_`, `_`-prefixed).
* A whole-project sweep (`experiments/AuditWholeProject.lean`) covered all **5,405** project constants (49 private). Their union of dependencies (68,385 constants) reaches the same three axioms and nothing else.

### Independent kernel replay

`leanchecker --fresh PrescribedExtinction.Theorem11` (the toolchain's checker) replays **every** constant in the import closure (Init, Lean, Std, Batteries, Mathlib, project) into an empty kernel environment. Result: exit 0 in 10 min 37 s.

This rules out environment hacking or declarations added without kernel checking. It does not provide an independent kernel implementation (see Limitations).

The proof of `theorem11` (`Theorem11.lean:11–47`) takes no hypotheses. Every structure it inhabits is constructed, so no hidden hypotheses can enter the final declaration.

---

## 2. Semantic fidelity: FAIL (the existence core passes)

### What is faithfully expressed (checked against the unfolded `#print` output in `logs/traversal.log`)

| Manuscript (p. 3) | Formal (file:line) | Check |
|---|---|---|
| Fix k>0, P>1, Q>0, E∗>0; ∀ 0<ϵ<1 ∃ body | `Maxwell.lean:115–117` | Same quantifiers, order and ranges. |
| Two adjacent homogeneous layers, common finite square aperture S_R=(−R/2,R/2)², D=S_R×(0,h+d), absorber below z=h, vacuum outside | `Basic.lean:47–77` | Constant tensors on an open box. Outside the box the permittivity is the identity. An open box is a.e. equal to the compact closed body. |
| εᵀ=ε, I ⪯ Re_H ε ⪯ PI, 0 ≺ Im_H ε ⪯ QI in both layers | `Basic.lean:34–39, 75–77` | `(v*εv).re` is the Re_H form and `(v*εv).im` the Im_H form. "∀v≠0, 0<Im" is ≡ 0≺Im_H in finite dimension. |
| μ=I, e^{−iωt}, curl E = ikZ₀H, curl Z₀H = −ikεE | `Maxwell.lean:58–62` | Signs correct for e^{−iωt}. |
| f± = e_y e^{±ikz}, Z₀H_inc,± = ±(e_z×e_y)e^{±ikz}, unit amplitude | `Maxwell.lean:31–39`, `planePhase_norm` (125) | Matches. |
| Distributional Maxwell equations, fields in H_loc(curl) | `Maxwell.lean:49–62` | All C_c^∞ complex vector tests against the bilinear pairing; curl is formally self-transpose, and the component formula was checked by hand. Interfaces are handled because the weak equation holds on all of ℝ³. |
| Uniform Silver–Müller condition on scattered fields | `Maxwell.lean:66–69, 79–80` | `‖x‖·‖Hs×x̂ − Es‖ < ε` for all ‖x‖ ≥ ρ. This is the correct sign for e^{−iωt}: an outgoing plane wave has H×x̂ = E. The condition is uniform over all directions. |
| X± (extinction cross-section) | `Maxwell.lean:96–97` | `k·Im∫_D f̄·χE`, the standard volume-work extinction for unit amplitude. See F3 for how this relates to the manuscript's definition. |
| A± (absorption) | `Maxwell.lean:100–101` | `k∫_D Im(Ē·εE)` = k∫Ē·Im_H(χ)E. This is the physical absorption cross-section. |
| Γ = \|A₊−A₋\|/X | `Maxwell.lean:109–110` | Divides by X₊, which equals E∗ > 0, so there is no division by zero. |
| X₊ = X₋ = E∗ exactly, 1−ϵ < Γ < 1 | `Maxwell.lean:120–123` | Matches. |
| Measure | `measureSpaceOfInnerProductSpace` | Haar measure normalized on an orthonormal box, i.e. Lebesgue measure. |

Name resolution was checked with `pp.fullNames`. `Field` and `Vector` resolve to the project abbreviations, not Mathlib's `Field` class or core `Vector`.

### Integrability (no exploitation of Lean's default zero integral)

All demonstrated in `experiments/AuditExperiments.lean`; each compiles with only the standard three axioms.

* **E4a** `auditor_extinction_pos_integrable` (l.89): `0 < extinction` forces the extinction integrand to be integrable. The final theorem asserts extinction = E∗ > 0.
* **E4b** `auditor_absorption_integrable` (l.113): for **every** `ScatteringState`, the absorption integrand is integrable on D. The proof uses Im(Ē·εE) = Im(Ē·P), E ∈ L²(D) and P ∈ L²(ℝ³).
* **E5** `auditor_weakMaxwell_integrands` (l.173): for **every** `ScatteringState` and **every** C_c^∞ test, all four weak-Maxwell integrands are genuinely integrable. The Maxwell equations therefore never hold as a default `0 = 0`.

### Findings affecting fidelity

**F1: Theorem 1.1's supremum clause is not formalized.** *Demonstrated discrepancy.*

* **Location**: manuscript p. 3, last italic sentence *inside* Theorem 1.1 (confirmed by rendering the page): "Consequently sup_{X=E∗} Γ = 1 in this class, and sup_{X=E∗} \|A₊−A₋\| = E∗." Section 8's status table also claims "Exact supremum 1, no individual positive-extinction equality".
* **Formal statement**: `PrescribedExtinction/Maxwell.lean:114–123` quantifies universally only over k, P, Q, E∗, ϵ. It contains no bound over arbitrary admissible bodies or arbitrary scattering states.
* **Consequence**: the Lean theorem certifies only the lower half (sup ≥ 1, by approach). sup Γ ≤ 1 requires passivity A± ≤ X for every admissible body and its fields, and sup \|A₊−A₋\| = E∗ needs the same. Neither appears in the statement.
* **What the repo does prove**: `physicalPerturbedAbsorption_le_extinction` (A ≤ X) only for its own constructed volume solutions.
* **Demonstration**: `#print OQ7Prescribed.Theorem11Statement` in `logs/traversal.log`.

**F2: The statement is existential over solutions; uniqueness and converse representation are not proved.** *Unproved; necessary for an exact match; mathematically true.*

* **Location**: `Maxwell.lean:75–81, 118–119`.
* **What exists in the repo**:
  * `ScatteringExistence.lean:99–104` (existence only).
  * `MaterialVolumeUniqueness.lean:74–80`, which proves uniqueness only *among solutions of the volume equation*.
  * No declaration in the repo takes an arbitrary `ScatteringState` as a hypothesis (grep). `README.md:44` acknowledges this.
* **Consequence**: `theorem11` shows that *some* pair of radiating weak Maxwell solutions has the stated cross-sections. The manuscript asserts properties of "the pair (1)", i.e. the unique outgoing solution. Its Lemma 2.1 claims uniqueness *and* the converse representation. The two statements coincide only if the radiating weak problem has at most one solution for the selected body. Uniqueness is not needed for kernel validity. It **is** needed to read the Lean theorem as the manuscript's physical claim.
* **Justification that the gap is benign** (sketch, not formalized): let (E,H) be the difference of two `ScatteringState`s.
  1. Over a ball B_r containing D, the weak curl identities give Re∫_{S_r} E·conj(H×x̂) = −k∫_D Im(Ē·εE) ≤ 0.
  2. Expand ∫_{S_r}\|H×x̂−E\|² → 0, which follows from uniform Silver–Müller. This gives ∫_{S_r}(\|E\|²+\|H×x̂\|²) ≤ o(1) − 2k∫_D Im(Ē·εE).
  3. Hence ∫_{S_r}\|E\|² → 0, and strict loss gives E = 0 a.e. in D.
  4. Rellich's lemma (componentwise Helmholtz outside D, where the fields are smooth) and unique continuation in the connected exterior of the box give E = 0, hence H = curl E/(ik) = 0.
  5. The pointwise form of `Outgoing` on representatives passes to the smooth exterior representative by continuity.

  So uniqueness holds, and under it the formal and physical statements of (4) agree.

**F3: X is formalized as volume work, not as A+S or via the forward optical theorem.** *Definitional identification; not a defect in (4), but part of (2) is not covered.*

* **Formal side**: `Maxwell.lean:96–97` defines X = k·Im∫ f̄·χE. The manuscript's (2) defines X = A± + S±, with S the total scattering cross-section, and uses the forward optical theorem in Lemma 1.2.
* **Unused definitions**: `scattering` (`Maxwell.lean:105–107`) is unused by the statement. Its own docstring (l.104) says its identification with outgoing flux is "still unproved".
* **Energy balance**: the repo's full-angle energy balance `physicalVolume_Haar_energy_balance` (`FarFieldWorkL2.lean:66`) is **not** in `theorem11`'s dependency cone (`logs/cone.log`). It uses a current far-field integral, not the Poynting flux of Es.
* **Consequence**: Γ is formalized in its first form \|A₊−A₋\|/X, which is the physically correct work form (sign checked for e^{−iωt}). The equalities X = A±+S± and Γ = \|S₊−S₋\|/X are not certified by the statement.

**F4: Strict nonattainment is proved only for the constructed body.** *Partly outside Theorem 1.1's (4).*

* **Formal route**: Γ < 1 is proved in `IsotropicPhysicalStrictLoss.lean:88–100` via A± > 0 (strict isotropic loss) and A± ≤ X. This is valid, and it is a different argument from the manuscript's Lemma 1.2.
* **What is missing**: Lemma 1.2's universal claim ("for every individual compact scatterer … X>0 ⇒ Γ<1", via far-field continuity and the optical theorem) is not formalized. Together with F1 it is what supports "sup not attained".

**F5 (historical): the original test class was vacuous.** *Demonstrated defect in the pre-correction target; fixed at the audited commit.*

* **Original**: `ContDiff ℝ ⊤ φ` (`verification/physical-target-before-test-correction.txt:50`; first commit `680cfab`). Here `⊤ : WithTop ℕ∞` means **ω, analytic**.
* **E2** `auditor_analytic_compactSupport_eq_zero` (l.29) proves that every analytic, compactly supported field on ℝ³ is 0. Consequently `auditor_old_weakCurl_vacuous` (l.43) proves the **old weak-curl condition holds for every pair (F, G)**. The original `WeakMaxwell` therefore reduced to local L² alone.
* **E7** `auditorOldIncidentState` (l.213) builds an old-definition scattering state, for **every** body, whose total field is the bare incident wave with zero scattered field. Under the original target the theorem was not about Maxwell fields at all.
* **Corrected**: `ContDiff ℝ (⊤ : ℕ∞)` at `Maxwell.lean:50`.
  * **E1** (l.23–24) proves `((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ ≠ ω`, i.e. C^∞.
  * **E3** `auditor_new_weakCurl_nonvacuous` (l.53) proves the corrected condition **rejects** "curl 0 = e_x", using a smooth bump test.
  * The corrected form is the standard distributional formulation (C_c^∞ test functions), matching the manuscript's "solve Maxwell's equations distributionally".
* **Repo characterization**: `TestRegularity.lean:3–6` and `README.md:40` call the original "weaker". That is accurate but understates it: the original imposed *no* equation.
* **History**: the final proof first appears at `5a8350d`, 41 commits after the correction `b7bbfe8`. It was never built against the vacuous target, and `Maxwell.lean:50` is the only change to the target since `680cfab` (`Basic.lean` is unchanged).

### Further semantic checks (no defect found)

* **Body**: the final body (`IsotropicPhysicalBody.lean:8–11`) is χ = αuuᵀ + iνI per layer. The absorber has α = iη, u = e_x. The plate has β = (p_j−1)+iδ, u = (cos θ, sin θ, 0). This matches manuscript (37).
* **Order of choices**: matches §5. The planar design is chosen first (`PlanarPrescribedDesign.lean:8`). Then the aperture and angle bracket (`PhysicalRankOneExtinctionBracket.lean:27`). Then ν < Q/3 (`PhysicalCompactLossBracket.lean:10`). Finally the intermediate-value angle (`PhysicalIsotropicPrescribedExtinction.lean:41`).
* **Uniform aperture localization**: `UniformBodyResponse.lean:9–15` is uniform over **all real θ**, including θ → 0, with R₀ depending only on (k, h, d, α, β, ε).
* **Volume operators**: the static and outgoing operators (contact term, signs, constants) are not part of the statement. Their correctness is nevertheless certified indirectly. The witness fields (`VolumeScatteringBridge.lean:101–109`) are proved to satisfy the corrected, non-vacuous `WeakMaxwell` and `Outgoing`. A wrong sign, constant or missing contact term would produce fields that are not Maxwell solutions, so the kernel-checked proof could not exist.
* **No conclusions embedded in definitions**: every definition in the statement is elementary (`logs/traversal.log`).
* **No vacuous structures**: `TwoLayerBody` and `ScatteringState` are both inhabited by the proof.

---

## 3. Mathematical completeness: FAIL (not established; no falsity found)

Everything `Theorem11Statement` needs is kernel-proved. Missing for the manuscript's full physical claim:

1. **Passivity for all admissible bodies and states** (Γ ≤ 1, \|A₊−A₋\| ≤ X), needed for the supremum clause (F1).
2. **Uniqueness of radiating weak solutions, or the converse volume representation**, needed to identify the witnesses with "the" physical fields (F2). Proof sketch above.
3. **The optical theorem and X = A+S with S the scattered Poynting flux over all angles** (F3). The repo's energy balance exists but is outside the cone and uses the current far field.
4. **Universal Lemma 1.2** (F4).

---

## Reproducibility and documentation findings (do not affect validity)

* **R1**: `lake-manifest.json` is git-ignored (`.gitignore:5`), so the commit alone does not pin transitive dependencies. The pins are in `sources/pinned-lake-manifest.json`, which is identical to Mathlib's manifest, so resolution is deterministic in practice.
* **R2**: `lakefile.toml:3` sets `packagesDir` to an absolute Windows path in a *shared, external* directory.
  * On Linux this creates a relative `C:/…` tree.
  * The colon breaks `lake env` (`LEAN_PATH` splits on `:`). I worked around this with a colon-free symlink to the same freshly built oleans.
* **R3**: `verify.ps1:22` runs `lake clean oq7_prescribed_extinction`, which cleans the project only. The dependency oleans come from the shared external directory and are never rebuilt. The repo's "clean build" therefore does not rebuild Mathlib, and its axiom audit (`collectAxioms` over loaded oleans) does no kernel replay. My from-source build and `leanchecker --fresh` close both gaps.
* **R4**: `Maxwell.lean:112–113` still says "an UNPROVED proposition. No proof declaration … is present". The docstring is stale.
* **R5**: `TestRegularity` is not in `theorem11`'s import closure. Its implication lemma is documentation only.

---

## Reproduction

```bash
# toolchain
curl -LO https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst
#   sha256 47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4; extract; put bin/ on PATH
lean --version            # … commit 5045d0056413266e57c625dcd7c365b10e377c52
git ls-remote https://github.com/leanprover/lean4.git refs/tags/v4.34.1
git ls-remote https://github.com/leanprover-community/mathlib4.git | grep d13f23b7

# isolated clone at the audit commit
git clone <repo> oq7 && cd oq7 && git checkout 5a8350d5408c38e333c9f6b6d8a94816c794120b
lake resolve-deps                         # cache fetch fails/declined → source build
lake build -v PrescribedExtinction.Theorem11   # 3494 jobs
lake build OQ7 PrescribedExtinction            # 3568 jobs

# LEAN_PATH workaround for the Windows packagesDir (see R2), then:
lean AuditExperiments.lean      # E0–E7
lean AuditTraversal.lean        # transitive traversal + unfolded #print of all statement definitions
lean AuditWholeProject.lean     # all 5,405 project constants
lean AuditCone.lean             # which key lemmas are in theorem11's cone
leanchecker --fresh PrescribedExtinction.Theorem11
```

The bundled `env.sh` holds the exact `LEAN_PATH` used.

### Logs (in `logs/`)

* `build-theorem11.log.gz` (verbose, 3494 jobs, `real 96m11s`, EXIT=0)
* `build-default-targets.log` (3568 jobs, EXIT=0)
* `leanchecker-fresh-theorem11.log` (EXIT=0, 10m37s)
* `experiments.log`
* `traversal.log`
* `whole-project-axioms.log`
* `cone.log`

---

## Limitations

* **Trust base**:
  * The Lean 4.34.1 release binary (downloaded, not compiled from source; no published checksum could be fetched to compare).
  * The standard meaning of Mathlib's definitions (`ContDiff`, Bochner integral, `MemLp`, `EuclideanSpace` measure).
  * `leanchecker` uses the same kernel implementation. No independent kernel (e.g. lean4lean) was run.
* **Not re-derived**: I did not re-derive the internal analytic lemmas (aperture localization, Green operators, planar slab algebra) by hand. For them I rely on the kernel check, which suffices for the Lean statement.
* **Uniqueness**: the argument in F2 is a sketch and is not formalized.
* **Repository scripts**: they are PowerShell and were not executed. Their substantive checks (pins, banned-token scan, build, transitive axioms, target hash `a9950f0f…` = README) were reproduced independently. The previous verification reports and AI audits were not relied on.
* **Manuscript reading**: read from extracted text plus a rendered page 3. Section 6 (bounded-resource asymptotics) is outside Theorem 1.1 and was not audited.
