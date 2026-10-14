# Lean statement correspondence and proof integrity

The current evidence supports one complete physical main theorem: **Paper A Theorem 5.1, FULLY KERNEL VERIFIED**. It supports independent generic coercivity/observable components and a complete **signed rational real-matrix SDP instance** of the overlap calculation. It does not support a full kernel proof of Paper A Theorem 7.1 or any of Paper B's actual Maxwell main theorems.

## 1. Actual sources and pins

The preserved actual scalar project is `../oq7` (named `scalar-lean` in the distribution ZIP). It contains 77 authored modules, 692 public theorem/lemma declarations and 1,288 kernel theorem constants, including helpers/generated equations. Its completed clean 3,043-job build is recorded at `2026-10-10T01:37:20.1349497Z`. In this mission, a separate inventory checked all 83 source/configuration hashes, all public exact types, all kernel axiom reports, nine pinned clean dependency revisions and an arbitrary-parameter import/application. It did not silently rebuild or change that preserved project. See `audits/LEAN_INVENTORY.md` and `existing-inventory.json`.

The new independent project is `lean/`, with three source modules `Coercivity`, `Observables` and `RationalOverlap`. Its final clean verifier exited zero at `2026-10-10T16:54:35.2839529Z`, including the frozen rational module. Its inventory has 35 public authored theorems, three private helpers, 61 kernel theorem constants and 70 total own constants, with zero declared mathematical axioms. `lean/verification/report.json` is the authoritative executed census, SHA-256 `70DD1B39DD3A34826E57CCD67A5A8B496B580FDFAA9ACC0E14B780696605C071`; exact public types are in `statements.log`, all kernel theorem axiom reports in `axioms.log`, and source/configuration/evidence hashes are recorded. All 31 new hash records match. Raw declaration counts are coverage checks, not counts of independent scientific advances. The new work comprises eight generic estimates and one explicit rational matrix optimization, with its supporting identities/positivity proofs.

Both projects pin:

* Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
* Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
* Full transitive revisions in their `lake-manifest.json` files.

The distinct reported 43-theorem Lean 4.19.0 supplement (Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`) was not recovered. Its PDF descriptions are not credited as actual source/build evidence. No supplied source was replaced by a theorem assuming the physical conclusion.

## 2. Complete scalar physical theorem

Exact exported type:

```lean
OQ7.theorem51 : ∀ (p : OQ7.PhysicalParameters), OQ7.Theorem51Statement p
```

`PhysicalParameters` requires positive k,Q,M, P>1 and the strict active target. `exactTargetClass` is defined from lists of actual homogeneous scalar layers with global `1≤p≤P`, `0≤q≤Q`, exact integrated loss M, total thickness at most L, exact transmitted power T and exact mean absorptance a. The transfer product, scattering amplitudes, flux/passivity and Helmholtz/Gram identities are proved from those layers. Construction and exact matching premises are discharged, rather than left as extra assumptions.

`Theorem51Statement` is the conjunction of eventual nonemptiness, strict finite-stack gap, and

```lean
Filter.Tendsto
  (fun L : ℝ => (p.k * L)^2 *
    (OQ7.ScalarEnvelope.D0 p.T p.a - OQ7.optimalAsymmetry p L))
  Filter.atTop (nhds (OQ7.asymptoticCoefficient p))
```

where the coefficient is `alpha*pi²*(k*M)^4/(3*P*Q²)`. The exact full type/definitions and source lines are retained in `Target.lean`, `SharpPhysicalConstruction.lean` and the full statement census. `audits/OQ7.theorem51-type.txt` preserves the exported type bytes. The final proof has no premise encoding a pre-existing sharpness construction or desired limiting bound.

## 3. New generic components: actual hypotheses and boundaries

These declarations live in `OQ7Mission`. E is a complex inner-product space; they are algebra/asymptotic estimates, not definitions of physical fields or Maxwell operators.

| Declaration | Exact substantive hypotheses and conclusion | Status / physical obligation |
|---|---|---|
| `norm_lower_bound_of_imaginary_coercivity` | c>0, any map L with `c||u||²≤-Im⟨u,Lu⟩` for every u implies `c||u||≤||Lu||` | FULLY KERNEL VERIFIED generic estimate; actual Maxwell coercivity must be proved separately |
| `current_error_le_residual` | Same coercivity and a bounded complex-linear L imply `||u-v||≤||Lu-Lv||/c` | FULLY KERNEL VERIFIED; no existence/surjectivity conclusion |
| `current_error_isLittleO_of_uniform_coercivity` | Family of bounded linear L_i with one fixed c>0, and residual error o(scale), imply current error o(scale) | FULLY KERNEL VERIFIED generic implication; actual residual/window estimate and varying-domain identification unproved in Lean |
| `quadraticWork_difference_bound` | Any bounded complex-linear A: `|Re⟨u,Au⟩-Re⟨v,Av⟩|≤||A||||u-v||(||u||+||v||)` | FULLY KERNEL VERIFIED; actual W and physical absorption identity unproved |
| `incidentWork_difference_bound` | `|Im⟨b,u⟩-Im⟨b,v⟩|≤||b||||u-v||` | FULLY KERNEL VERIFIED; incident normalization/optical interpretation unproved |
| `quadraticWork_difference_isLittleO_square` | Uniformly O(1) operators, currents O(scale), current difference o(scale) imply quadratic work difference o(scale²) | FULLY KERNEL VERIFIED generic asymptotic estimate |
| `incidentWork_difference_isLittleO_square` | Incident vector O(scale), current error o(scale) imply imaginary work error o(scale²) | FULLY KERNEL VERIFIED generic estimate |
| `area_normalized_work_errors_tendsto_zero` | The preceding boundedness/error hypotheses imply work, incident-work and their difference divided by scale² tend to zero | FULLY KERNEL VERIFIED generic normalized convergence; the work difference is not called sphere radiation without an independently proved optical theorem |

The full exact elaborated types, including every typeclass and filter hypothesis, are exported by the verification script. Hypotheses such as coercivity or a small residual are appropriate in these clearly identified generic lemmas. They are not hidden as an asserted physical theorem. No declaration named Maxwell localization claims to derive those premises from a real Green operator.

## 4. Exact rational overlap optimization

Namespace: `OQ7Mission.RationalOverlap`. `Mat2` is `Matrix (Fin 2) (Fin 2) ℝ`. Definitions are actual real matrices:

`B=(1/190)[[139,17√21],[17√21,71]]`, `W=diag(9/10,-1/10)`,

`Z=[[7/8,-17√21/168],[-17√21/168,3/8]]`, `E=[[0,1/2],[1/2,0]]`,

`nu=-19√21/42`, `H=(1/8)[[7,√21],[√21,3]]`.

The source proves the Lyapunov identity `BZ+ZB=W`, det Z=19/168, H=Z-nu E, H(I-B²)=0, tr(WB)=59/95, the exact contrast, and genuine Mathlib PSD/contraction predicates. Explicit quadratic decompositions justify positive trace pairings, not assumed nonnegative certificate remainders.

The exact main upper bound is:

```lean
theorem rational_SDP_upper_bound (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : (W * A).trace = 59 / 95) :
    2 * (3 / 5 : ℝ) * Q 0 1 ≤ 1071 * Real.sqrt 21 / 9025
```

`rational_SDP_attainment` gives actual A,Q satisfying these conditions and equality, using A=B,Q=B². `rational_square_upper_bound` supplies the Q=A² specialization. The full three-trace identity is proved for arbitrary real symmetric variables and the sign nu<0 is derived. This is a complete optimization of the stated **signed** objective in this real two-dimensional relaxation at the rational target. It is not a Lean proof of the canonical optical reduction, the absolute-contrast sign transformation, the generic parameter strip or local Maxwell realization. Full Theorem 7.1 therefore remains **PARTIALLY FORMALIZED**.

## 5. Main manuscript correspondence

| Manuscript result | Actual declaration/evidence | Mathematical assumption correspondence | Status | Unproved dependencies |
|---|---|---|---|---|
| A4.2 capped moment | `OQ7.capped_fourier_moment`, `capped_fourier_moment_Ioo` | Integrable capped q, positive K,Q, interval≤π/K; exact norm integral | FULLY KERNEL VERIFIED | None for the stated integral/cap declarations |
| A4.4 convexity/tangent | `OQ7.ResourceScalar.g_convex_half`, `g_tangent_full` | Exact intervals and small positive tangent location | FULLY KERNEL VERIFIED | None |
| A4.5 full selected-material floor | `OQ7.theorem45_finite`, `theorem45_uniform_asymptotic`, `theorem45_sequence_lowerlimit` | Lean additionally imposes global p≥1 | PARTIALLY FORMALIZED | Extend actual physical model/proofs to the broader real-permittivity class; cannot erase the extra premise |
| A5.1 | `OQ7.theorem51` | Exact scalar physical targets, caps, mass, thickness, all-budget limit | FULLY KERNEL VERIFIED | None for this exact main statement |
| A6.2 general/equality channel theorem | No complete available declaration; historical finite-column theorem unavailable | Arbitrary coherent Hilbert inputs/background are not supplied by a finite-column description | ORDINARY PROOF ONLY | Complete general channel/equality formalization |
| A6.3 scalar normalized optimum | No available complete declaration | Golden-ratio optimization/all phase equality cases | ORDINARY PROOF ONLY | Exact scalar optimum and equality classification |
| A6.4 / Cor.6.5 | No physical tensor/beam declaration | Infinite planar tensors and power-normalized angular spectra | ORDINARY PROOF ONLY | Actual tensor transfer, beam continuity, IVT and ordered limit |
| A7.1 | New exact rational SDP upper bound/attainment | One signed real relaxation instance only | PARTIALLY FORMALIZED | Full canonical channel reduction, parameter identities/uniqueness, all branches/transitions, all equality operators |
| B2.1 | No complete available dipole theorem | Actual six-coordinate radiation/reciprocity/polarizability definitions absent | ORDINARY PROOF ONLY | Full dipole optical theorem and contraction correspondence |
| B3.2-6 analytical Maxwell foundation | Generic norm/work components only | Physical operators, equations, fiber identities are not defined by generic E,L,A | ORDINARY PROOF ONLY for manuscript statements | Distributional Green, outgoing weak equivalence, strict-loss solvability, sphere radiation and Weyl estimates |
| B3.1 localization | No physical main declaration | Actual finite aperture/material/current/cross-section convergence absent | ORDINARY PROOF ONLY | All Maxwell foundations, mixed-norm commutator, window density, observable identification |
| B3.8 rate | No complete declaration | Physical window/fiber/geometry construction not formalized | ORDINARY PROOF ONLY | Quantitative square cutoff, Fourier decay, fixed-stack rate constants |
| B3.9-10 | No physical construction declaration | Finite planar tensors and δ-continuity absent | ORDINARY PROOF ONLY | Exact arbitrary-cap plate/absorber, passive boundary solve, positive-loss regularization |
| B3.11 / B1.1 | No physical compact supremum declaration | Exact local finite 3D dielectric class/cross sections absent | ORDINARY PROOF ONLY | B3.1 plus actual planar construction, ordered choices, optical nonattainment |

There is no claimed CONDITIONALLY VERIFIED complete Maxwell theorem: no formal main proposition over actual Maxwell definitions was built. The generic proved implications do not justify upgrading physical results to that status. No actual main theorem is marked FAILED because no genuine counterexample was found.

## 6. Axioms, named dependencies and integrity controls

Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. Both audits reject `sorryAx`, declared extra axioms and native-decision proof mechanisms. Every imported kernel theorem in each own namespace is audited, including helper/generated constants. Exact types, direct used-constant edges from types and proof terms, recursive dependency records, and transitive axiom results are preserved. The final dependency export distinguishes project-local closure from the full recursive Mathlib/Lean closures for the selected main results. `verification/full-dependencies.json` contains 18,745 nodes and 440,717 type/value edges for the new principal results; `full-theorem51-dependencies.json` contains 50,626 nodes and 1,719,459 edges for theorem51, including 50,625 transitive named constants. Every selected root reaches precisely the three accepted foundational axioms. Pinned source and manifests resolve the library definitions.

The independent harness accepted a valid arbitrary-parameter A5.1 application and rejected five isolated invalid/admitted/axiomatic controls. A false `rfl` proof failed compilation. `sorry` and `admit` compiled with exit zero but were rejected by `sorryAx`. A used axiom was rejected through transitive dependencies, and an unused axiom was rejected by the declaration census even though its harmless theorem had no such dependency. All six cases matched expected outcomes and all original 83 hashes stayed unchanged.

Bad fixtures deliberately contain forbidden mechanisms. They are isolated under `integrity-tests/`, excluded from accepted proof libraries, and are evidence of rejection rather than accepted mathematical source. Controls test audit enforcement, not compiler soundness.

## 7. Clean reproduction

On the original PC, follow `lean/README.md` for the portable compiler/cache path and run from `lean/`:

```powershell
.\bootstrap-cache.ps1
.\verify.ps1 -Clean
```

On another machine, obtain the official pinned Lean release and resolve dependencies from the manifest; dependency caches and binaries are not shipped. The ordinary `lake build` target is a real source library. The explicit audit runs separately and must succeed as well as the build. The original project independently supports `verify.ps1 -Clean -Milestone theorem51-independent`. Re-running it changes its generated evidence logs, so the mission itself preserved that older evidence and audited it read-only.

## 8. Remaining formal work, without model substitution

To complete A7.1, prove the actual background antiunitary/canonical congruence, real two-plane compression, both sign reductions, generic c/λ identities and positivity, monotone parameter existence/uniqueness, PSD certificate for all parameters, plateau/last-branch necessity and constructions, endpoint/equality classifications. The rational module supplies none of the general quantifier reductions automatically.

For B, construct actual L²/Sobolev vector fields and distributions, outgoing Helmholtz fundamental solution and vacuum uniqueness, singular-integral/Schur operators, weak Maxwell/VIE equivalence, exact sphere radiation and optical theorem, bilinear reciprocity, uniform strict-loss solvability, outgoing Fourier boundary fibers, local mixed-norm commutator and density, scaling/window geometry, planar tensor transfer/regularization, and the ordered compact supremum construction. These are substantial infrastructure obligations; assuming them would not constitute completion. The analytical audit precedes and supports this work, but is not a kernel substitute.
