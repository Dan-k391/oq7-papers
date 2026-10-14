# Research Verification Mission: OQ7 Mathematical Audit and Lean Formalization

## Mission

Conduct an independent, adversarial mathematical audit and rigorous Lean 4 formalization of two research manuscripts:

**Paper A:** *Reciprocal absorption–scattering asymmetry: sharp channel bounds, exact vector dielectric constructions, and a restricted thickness law* (10 October 2026, 41 pages).

**Paper B:** *Compact reciprocal Maxwell scatterers can approach unit absorption asymmetry* (10 October 2026, 24 pages).

These papers investigate Open Question 7 (OQ7) from Miller and Monticone, *Fundamental Limits in Photonics and Electromagnetics: A Tutorial* (arXiv:2605.24738).

The ultimate goal is to determine whether the manuscripts contain mathematically correct, physically faithful, and independently certifiable results, particularly the claimed resolution of the resource-unrestricted compact 3D Maxwell absorption-asymmetry problem.

**Do not assume either manuscript is correct. Your role is to attempt to falsify its claims before accepting them.**

Use extensive mathematical reasoning, independent proof reviews, numerical counterexample searches, and Lean 4 formalization.

## 1. Establish the exact mathematical claims

Read both manuscripts in full, including their appendices, proofs, hypotheses, and references.

Extract every major theorem, proposition, and lemma into a dependency graph.

Prioritize the following results.

### Paper A

- Theorem 4.5: finite material-resource determinant lower bound.
- Theorem 5.1: sharp inverse-square thickness asymptotic for scalar dielectric multilayers.
- Theorem 6.2: general-channel extinction–absorption bound.
- Theorem 6.3: sharp scalar two-port contrast bound.
- Theorem 6.4 and Corollary 6.5: exact anisotropic dielectric realizations and finite-power beams.
- Theorem 7.1: sharp three-branch extinction–time-reversal-overlap tradeoff.

### Paper B

- Theorem 1.1: unrestricted compact dielectric supremum.
- Theorem 2.1: radiation-consistent electric–magnetic dipole bound.
- Theorem 3.1: exact Maxwell finite-aperture localization theorem.
- Lemmas 3.2, 3.4, 3.6 and the relevant supporting propositions.
- Proposition 3.8: quantitative square-aperture convergence rate.
- Lemmas 3.9–3.10: physical planar construction and positive-loss regularization.
- Theorem 3.11: compact local nonmagnetic dielectric supremum.

For every result, identify the exact hypotheses, conclusion, dependencies, physical interpretation, and current verification status.

Do not silently strengthen, weaken, or change theorem statements.

## 2. Independent adversarial mathematical audit

Conduct at least three logically independent investigations, using separate agents or reasoning approaches if available.

**Audit A: Analytical correctness**

Re-derive the proofs from definitions and established theorems, without relying on the manuscript's conclusions.

Check every nontrivial inequality, limit, exchange of integrals, operator estimate, compactness argument, differentiability assertion, and application of the implicit function theorem.

Identify unstated assumptions and determine whether they are essential.

**Audit B: Counterexamples and edge cases**

Actively search for counterexamples to every major claim.

Investigate degenerate inputs, singular matrices, resonances, grazing incidence, zero or vanishing loss, thin-layer limits, unbounded geometry, and failures of uniform convergence.

Use arbitrary-precision computation and numerical optimization when useful, but never treat numerical success as proof.

**Audit C: Physical and mathematical model fidelity**

Verify that the stated mathematical models genuinely describe reciprocal passive Maxwell systems.

Check electromagnetic boundary conditions, power normalization, the optical theorem, reciprocity, causality, polarization conversion, and radiation into all directions.

Ensure no outgoing channels or diffracted fields are omitted.

Each audit must produce its own written findings before the results are reconciled.

Classify each detected issue as:

- Fatal theorem failure.
- Proof gap with a potentially correct theorem.
- Missing or unjustified assumption.
- Correctable technical error.
- Expository or notation issue.

For genuine errors, provide either a counterexample or a corrected rigorous proof.

Never conceal a failed audit.

## 3. Highest priority: Independently verify Paper B, Theorem 3.1

This is the most important and difficult part of the project.

Theorem 3.1 claims that finite-aperture truncations of a fixed strictly absorbing planar dielectric stack have absorption, extinction, and total scattering cross sections that converge, after normalization by aperture area, to their exact planar counterparts.

This theorem bridges infinite planar optics and finite compact three-dimensional Maxwell scatterers.

**Audit every step independently.**

In particular:

1. Verify the electric Maxwell volume-integral formulation and the correspondence between the integral equation and outgoing weak Maxwell solutions.

2. Check the distributional dyadic Green operator, including singular kernels, local terms, and the claimed boundedness on the relevant function spaces.

3. Verify the operator identity

   `L_R = χ⁻¹ − T_R`

   and all assumptions needed for its meaning and invertibility.

4. Independently derive the coercivity estimate and confirm that its constant is genuinely independent of aperture size when the material parameters are fixed.

5. Check the full-space Fourier decomposition, the outgoing Weyl representation, and the treatment of propagating versus evanescent transverse wave numbers.

6. Investigate the singular behavior near the grazing circle `|κ| = k`, where the Green-fiber norm has a potentially problematic singularity.

7. Verify the smooth-window commutator estimate, including its Fourier-domain justification, function-space domains, and approximation arguments.

8. Check every step leading to

   `||P_R − q||_{L²(D_R)} = o(R)`.

9. Verify the conversion from current convergence to absorption and extinction cross-section convergence.

10. Prove that the complete scattered power converges, including edge diffraction, polarization conversion, and all outgoing solid angles.

11. Independently derive the claimed `O((kR)^(-1/3))` square-aperture error estimate and verify the dimensional consistency and dependence of its constants.

12. Check the order of limits used when absorption loss, extinction, thickness, and aperture size vary.

Pay special attention to places where a formally plausible estimate might fail because its constant depends on aperture size or because a singular Green operator is being controlled in the wrong norm.

**Do not accept Theorem 3.1 until every functional-analytic bridge is justified.**

If it fails, determine whether a weaker localization theorem can be rigorously established without changing the meaning of the original result.

## 4. Verify the compact supremum theorem

Audit the claim

`sup Γ = 1`

where

`Γ = |σ_abs,+ − σ_abs,−| / σ_ext`

for compact reciprocal dielectric bodies with fixed frequency and fixed upper material-property bounds.

Independently verify:

- The exact two-layer planar construction.
- The prescribed bounds on real and imaginary permittivity.
- Passive reciprocal anisotropic dielectric behavior.
- Positive-loss regularization.
- Continuity of the planar scattering observables.
- Application of the localization theorem.
- The diagonal construction yielding finite compact objects.
- Nonattainment of Γ = 1 for each individual regular compact object with positive extinction.

Check whether the stated construction truly works for every fixed `P > 1` and `Q > 0`.

Distinguish clearly between:

1. Arbitrarily close asymmetry in an infinite slab.
2. Arbitrarily close asymmetry for finite-power beams.
3. Arbitrarily close asymmetry for compact finite 3D objects under plane waves.

Only the third establishes the paper's central compact-object claim.

## 5. Verify the major results of Paper A

### Theorem 5.1

Independently audit the full sharp thickness law

`lim (kL)² [D₀ − D*(L)] = α π² (kM)⁴ / (3 P Q²)`.

Recheck the Gram determinant identity, complex modulus comparison, capped Fourier moment bound, cell determinant inequality, convexity and global tangent arguments, uniform finite-thickness lower bound, asymptotic construction, lossless coating invariance, physical matching networks, and implicit-function argument preserving exact transmission and mean absorptance.

Check both the universal lower estimate and the physically realizable matching upper construction.

### Theorem 7.1

Re-derive the three-branch sharp tradeoff with prescribed extinction and time-reversal overlap.

Verify the canonical coordinate reductions, matrix compression, positive-semidefinite certificate, equality cases, uniqueness of the middle-branch parameter, and transition conditions.

Test the exact rational example independently.

Determine whether the claimed abstract equality matrices admit local Maxwell realizations, or identify the remaining realization gap.

Do not confuse an abstract matrix theorem with a theorem about actual electromagnetic bodies.

## 6. Full Lean 4 formalization

Use Lean 4 and Mathlib.

First inventory all supplied Lean source files, existing projects, toolchain versions, theorem statements, build logs, and axiom reports.

A previous project reportedly contained approximately 692 public theorems, including `OQ7.theorem51`, using Lean 4.34.1.

Another project reportedly contained 43 authored theorems using Lean 4.19.0.

These reports are not substitutes for the actual source code.

If the 692-theorem project is unavailable, explicitly identify it as missing. Do not claim to have recovered, verified, or reproduced it.

Preserve existing projects and build independent verification modules.

### Formalization strategy

Proceed in stages:

**Stage A: Algebraic results**

Formalize the exact scattering-matrix definitions and prove the main passive reciprocal channel bounds and equality constructions.

Formalize the complete three-branch Theorem 7.1, including sharpness and all transition regions, rather than merely its generic positive-matrix certificate.

**Stage B: Scalar physical results**

Formalize the actual one-dimensional Helmholtz model, material admissibility, scattering coefficients, energy identities, and as much of Theorem 5.1 as possible.

Where the original project already has valid formal proofs, reuse them after checking theorem equivalence and dependencies.

**Stage C: Maxwell analytical foundations**

Construct the mathematical infrastructure needed for Paper B:

- Complex vector fields and Hilbert spaces.
- Distributional or suitable weak Maxwell equations.
- Electromagnetic Green operators.
- The volume-integral formulation.
- Reciprocity and passivity identities.
- Full-sphere far-field radiation.
- Optical-theorem identities.
- Fourier-fiber operators and convergence estimates.

Prove the required supporting results rather than postulating them.

**Stage D: Theorem 3.1**

Formalize the finite-aperture localization theorem with the actual Maxwell volume-integral operators and convergence of physically defined cross sections.

This is the primary formal-verification target.

**Stage E: Theorem 3.11 and Theorem 1.1**

Formally derive the compact supremum from the physical planar construction, positive-loss regularization, localization theorem, and optical theorem.

Keep the original scientific hypotheses intact.

### Strict Lean requirements

- No `sorry`.
- No `admit`.
- No `sorryAx`.
- No unauthorized new axioms.
- No theorem statements that merely assume the desired conclusion.
- No `native_decide` or unsafe shortcuts that bypass the intended trusted kernel proof.
- Do not replace Maxwell scattering with an abstract matrix model while retaining the same theorem label.
- Do not hide difficult mathematical claims inside opaque assumptions or unverified external routines.

Standard Lean foundations such as `propext`, `Classical.choice`, and `Quot.sound` are acceptable.

A theorem may depend on named intermediate lemmas only when those lemmas are themselves proved, or explicitly identified as unproved dependencies.

Use `#print axioms` and an automated dependency census for every main result.

Prove that the audit detects deliberately introduced invalid proofs or admitted assumptions.

Provide exact reproducible commands for clean builds.

## 7. Statement correspondence and proof integrity

For every major manuscript result, create a formal correspondence table:

| Paper theorem | Lean declaration | Mathematical assumptions | Verification status | Unproved dependencies |
|---|---|---|---|---|

Use the following precise statuses:

- FULLY KERNEL VERIFIED: The actual main result follows from proved formal definitions and lemmas.
- CONDITIONALLY VERIFIED: The final implication is formalized but depends on a substantial unproved physical or analytical theorem.
- PARTIALLY FORMALIZED: Only selected components are verified.
- ORDINARY PROOF ONLY: A mathematical proof exists but is not formally verified.
- FAILED: A counterexample or genuine proof error was found.

Never label a mathematical result FULLY KERNEL VERIFIED when its core physical or analytical theorem has been assumed.

For each verified theorem, preserve its exact Lean statement, transitive dependencies, and axiom report.

## 8. Reproduce the numerical calculations

Independently reproduce the manuscripts' major numerical examples.

For Paper B, verify the complete dipolar radiation power, full-sphere scattering identity, finite-aperture discrete-dipole results, and convergence toward the planar reference.

Investigate the reported mesh sensitivity and failed iterative solver runs.

Where feasible, use independent algorithms rather than re-running the author's implementation.

Distinguish:

- Exact symbolic identities.
- Numerically converged discrete models.
- Continuum-converged results.
- Analytical theorems.

Do not present numerical agreement as proof of a continuum Maxwell theorem.

## 9. Literature and originality review

Search the literature for mathematically equivalent results, not only similar titles.

Pay special attention to:

- Sounas and Alù's reciprocity and extinction results.
- Guo and Fan's reciprocal scattering constraints.
- Hopkins et al.'s directional absorption work.
- Mann and Alù's 2023 maximum-asymmetry dipole results.
- Gao, Yang and Kattawar's finite-plate convergence results.
- Mathematical electromagnetic volume-integral theory.
- Large-aperture scattering and Fourier localization theorems.
- Observability and matrix-optimization theorems relevant to Papers A and B.

Distinguish proof correctness from scientific novelty.

Neither a Lean proof nor an unsuccessful literature search establishes novelty.

## 10. Required deliverables

Produce the following artifacts in a reproducible research directory.

**A. `MATHEMATICAL_AUDIT.md`**

Complete theorem-by-theorem findings, with counterexamples or corrected proofs for any discovered issues.

**B. `MAXWELL_LOCALIZATION_AUDIT.md`**

A detailed independent reconstruction of Paper B, Theorem 3.1. Every analytical estimate must be accounted for.

**C. `LEAN_STATUS.md`**

Exact source declarations, build results, axiom reports, unproved dependencies, and differences between the formal statements and manuscripts.

**D. `NOVELTY_REVIEW.md`**

Source-by-source prior-art comparison, including unresolved publication-access limitations.

**E. `VERIFICATION_REPORT.md`**

A concise final assessment explaining which results are genuinely verified, which remain conditional, and whether either manuscript's main claim survives the audit.

**F. Complete Lean project**

Include source files, pinned toolchain and Mathlib revisions, project manifests, scripts, build logs, and theorem/axiom census.

**G. Revised manuscripts**

Only if substantive corrections are needed. Preserve the originals unchanged and document every modification.

## 11. Research execution rules

Work autonomously through the mathematical audit, targeted repairs, and formalization as far as the available tools and resources permit.

Prioritize correctness over the number of verified theorems.

Do not inflate theorem counts using trivial results.

Do not claim successful Lean verification without actual source code, a successful build, and an axiom audit.

When full formalization is not feasible within the available resources, deliver meaningful independently checked components, identify the exact remaining proof obligations, and provide reproducible source code.

Do not convert an unfinished proof into a claimed success.

If a major theorem is false, stop treating it as established and document the failure clearly. Continue with corrected or weaker statements where scientifically useful.

Do not report AI-agent agreement as independent human peer review.

## 12. Final research verdict

Answer these questions explicitly:

1. Is Paper A, Theorem 5.1 mathematically correct?
2. Is Paper A, Theorem 7.1 mathematically correct?
3. Is Paper B, Theorem 3.1 mathematically correct under its exact hypotheses?
4. Does Paper B rigorously prove `sup Γ = 1` for actual compact 3D Maxwell scatterers?
5. Which complete results have been kernel-verified in Lean?
6. Which proof gaps or model-fidelity issues remain?
7. Are the main contributions plausibly novel?
8. What exactly has been resolved about the original OQ7?
9. What must happen before the results are suitable for public dissemination or journal submission?

**The ultimate success criterion is trustworthy mathematical certification, not a positive verdict. Finding a fatal error is a successful audit outcome if the error is real.**

Begin with the complete independent mathematical audit of Paper B, Theorem 3.1, before allocating major resources to full Maxwell formalization. Then audit Paper A and build Lean proofs based on the results that survive scrutiny.