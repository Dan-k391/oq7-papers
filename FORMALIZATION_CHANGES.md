# Lean formalization changes — 15 October 2026

This record concerns the generalized-research and quartic-Maxwell manuscripts.
Work started from repository commit `2c8e3a4` after pulling `main`. The primary
working clone is `D:\oq7-papers`.

## Preservation

- The dated source PDFs, historical manuscripts, sealed review packages,
  original mathematical audits and existing prescribed-extinction Lean sources
  are preserved. New proofs live in separate per-paper formalization projects.
- Lean remains 4.34.1 (compiler commit
  `5045d0056413266e57c625dcd7c365b10e377c52`); Mathlib remains
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Dependency sources were restored from the repository's pinned snapshots.
  The official Windows compiler archive passed the recorded SHA-256 pin
  `457698d4e2132243e899ff32178d7ae63c16431d09ed9ad524d859c3581992af`.
  Toolchains, dependency caches, compiled objects and scratch files are ignored.

## Generalized-research project

New sources under `papers/generalized-research/formalization/` provide:

- A version-specific correspondence wrapper for the existing exact-target
  physical thickness theorem, including its actual layer class and proved
  Maxwell/Helmholtz and interface identities.
- A new minimum-thickness corollary for an infimum over actual exact-target
  finite stacks. The proof does not assume an attained optimum. It proves
  near-optimal feasibility, the normalized limit, the literal leading constant
  in the manuscript, and divergence of the required thickness.
- Arbitrary-Hilbert-space power identities, passivity parabola and equality
  condition; genuine antiunitary reversal and extinction reciprocity; and
  lossless-background normalization preserving the actual powers.
- An actual Hilbert input-plane compression: its positive slack is the Gram
  matrix of projection residuals. Phase normalization constructs the required
  conjugation-fixed frame from an arbitrary input/reverse pair.
- A continuously parameterized middle-branch positive-matrix certificate,
  parameter existence and uniqueness, the full canonical three-branch upper
  envelope, absolute/sign symmetry, transition values and equality constraints.
- Literal complex finite-channel equality constructions for the first,
  middle and third branches, including signed-forward reversal and the
  orthogonal-pair passivity endpoints.
- A complete same-Hilbert-space upper and attained-lower overlap theorem,
  including a lossless bounded-map reference whose surjectivity is derived
  from reciprocity and its isometry identity.
- Full complex scalar two-port feasibility and the active/plateau ceiling,
  every endpoint, the fixed-extinction curve and golden-ratio maximum.
- The complete original feasibility proposition, including the actual
  prescribed-entry argument/cosine phase criterion and its zero-amplitude
  determinant clause. The underlying complex positive-matrix criterion and
  interference identity are proved, rather than assumed.
- The complete golden-ratio equality family: necessity and sufficiency for
  every real reflection phase, including port interchange. Tightness in the
  polynomial certificate forces the exact scalar parameters; actual passivity
  then forces the signed reflection product. These clauses were checked against
  the original numbered statements before the final proof graph was frozen.
- Actual homogeneous plate/slab Maxwell fields, three-dimensional material
  tensors, interface and external boundary matching, literal four-port
  scattering, and the simultaneous weak-loss/thick-absorber limit.
- Actual finite scalar multilayers approaching the golden-ratio contrast,
  with exact material and power targets and a counted, bounded-index
  reflectionless dielectric phase-correction layer.
- A broader piecewise Helmholtz-profile resource proof allowing arbitrary
  real permittivity, with the transfer determinant, flux Gram, passivity,
  selected-cell floor and uniform limit derived from the differential equations.
  Explicit zero/negative real-permittivity examples and the old-stack embedding
  distinguish this extension from the earlier globally positive class.

The first complete checkpoint passed all 39 compilation steps, an exhaustive
1,007-declaration exact-type and transitive-axiom audit, and fresh kernel replay.
Its source snapshot and original/current manuscript correspondences are saved
under `verification/checkpoint-main-claims/`.

Further proofs compile for the literal at-most-three-channel equality
construction and continuity of the implicitly parameterized envelope, including
both transitions. Actual transverse-momentum reversal of the oblique material
response and vacuum reference is proved, including the literal reversed
finite-power packet.

A new physical Fourier wrapper corrects Mathlib's standard 2π convention to
the manuscript's physical wave vector. Its two-dimensional change of variables
proves exact L² norm and inner-product preservation. For L¹ ∩ L² spectra,
tempered-distribution pairing and uniqueness identify the wrapper with the
literal `(2π)⁻¹ ∫ exp(i κ·x) f(κ) dκ` integral almost everywhere. These proofs
compile without warnings. Actual oblique Maxwell transfers, spatial
superposition, classical regional curls, interface matching, finite transverse
L² fields, physical square-root-two power normalization, total boundary
interference cancellation and exact finite-power Poynting absorption are joined
in the beam corollary. The same actual capped design has unit-power inputs,
literal background time reversal, exactly prescribed common extinction, the
sharp parabola supremum and relative-contrast supremum one.

The last cell-lemma work explicitly changes from fundamental fields to the
actual unit-incidence scattering fields and constructs the complementary
positive Gram matrix for arbitrary finite disjoint cells. The latter does not
assume an equal-width partition. These additions enter the final combined
replay. Complete unnumbered optimizer phase/spectrum classifications and the
strict nonattainment remark remain separate obligations. No assertion that
every sentence or displayed auxiliary identity has been formalized is made.

## Quartic-Maxwell project

New sources under `papers/quartic-maxwell/formalization/` provide:

- The shared-inverse radiation-quadratic estimate with the exact `2/(3π)`
  coefficient, under explicit operator hypotheses.
- Genuine imaginary-coercive invertibility and the sharp inverse-loss
  resource factor `m/M²`.
- Oscillatory Green-function cancellation proved by a derivative integral,
  followed by the exact radial/tangential dyadic decomposition and the sharp
  actual-kernel bound `3k²/(8π‖x‖)`.
- Exact three-dimensional Newton-ball integrals, translated rearrangement for
  arbitrary bounded measurable supports, and the volume radius
  `a_v=(3V/(4π))^(1/3)`.
- A vector Schur estimate with integrability derived from row/column bounds;
  its application to the actual support-masked Maxwell remainder; the exact
  `3k²a_v²/4` difference bound and static Fourier contraction bound.
- Quotient-remainder, positive-coefficient and origin-translation lemmas,
  kept separate from the physical coefficient and sphere-response obligations.
- Re-runnable arithmetic certificates retained as arithmetic results, without
  claiming that their constants prove actual continuum sphere responses.
- The actual full-angle L² radiation map, exact sphere moment, sharp norm,
  compact-current far-field normalization and genuine imaginary-Green work.
- Actual bounded-support plane waves, their exact source norms and paired
  difference estimate, L² conjugation and genuine Green reciprocity.
- A constructed measurable tensor multiplier on the support-restricted L²
  space, with its norm, coercivity, inverse, pointwise constitutive equation
  and exact inverse-loss factor derived from the original material assumptions.
- The actual common material/Green inverse, reciprocal forward work, power
  balance, positive extinction and the full uniform quartic bound and ball
  corollary, without assumed analytic operator estimates.
- Arbitrary-direction transverse vacuum plane waves; actual locally L²,
  outgoing weak Maxwell solutions; and the converse representation and
  uniqueness for every independently supplied weak state.
- Physical material-loss and incident-work integrals, complete far-field and
  Poynting-flux scattering, optical balance and exact reciprocal extinction.
  The uniform upper theorem is exported directly for these physical weak states.

The full upper-theorem checkpoint passed all 26 ingredient-module builds, a
300-declaration exact-type and transitive-axiom audit, and fresh kernel replay.
It is preserved separately under `verification/checkpoints/upper-2026-10-14/`.

Thirteen further modules have compiled and passed a 187-export standard-axiom
audit. They establish the actual incident-source Taylor bounds, static
resolvent estimates, radiation-Gram evenness/moments, physical fixed-pattern
coefficient and explicit sixth-order error. The spatial dilation proof derives
the three-dimensional Jacobian, locally square-integrable weak curls, full
radiation condition, admissible scaled medium and exact absorption/extinction
scaling from their definitions. The fixed-wavenumber shrinking-body theorem
quantifies over every actual outgoing weak state. The combined 39-module,
487-export checkpoint has passed compilation, exact-type/axiom audit, its
62-root completeness guard, and fresh kernel replay with unchanged source hashes.

The actual solid-ball Newton potential, interior static operator response,
arbitrary-input mean response and separated-support Newton-Hessian association
have compiled separately. Sharp Hessian norm/difference and rectangular
cross-block bounds also have actual kernel proofs. Three new staged modules
derive the actual exterior ball field, continuity of its Hessian convolution,
the pointwise single-ball Hessian mean and the exact double-ball mean. They
pass through the actual volume Newton potential, translated compact tests,
static Fourier-field identification and an almost-everywhere-to-pointwise
continuity argument.

The heterogeneous remainder module uses the literal finite two-sphere medium,
its volume and actual dynamic solution bounds. It derives the paper's signed
scattering error `168 w² t³/(25π)` and forward-work error `108 w t²/25`.
The actual two-ball inverse and moment assemblies now give the full
heterogeneous certificate: coefficient in `[36/1299125,44/1295875]`, remainder
`21 t^6/2000` for `0<t<=1/4`, and lower bound `27 t^4/1299125` for
`0<t<=1/40`. Fixed physical wavenumber statements quantify over every
independently supplied outgoing weak state.

For homogeneous material, the first-interaction moment is derived from the
actual finite-sphere inverse and exact Hessian means. Centered affine currents,
odd-current cancellation, all remaining static interactions, and quantitative
moment errors are included. One relative sphere radius depends only on the
loss parameter and is fixed before shrinking. The final supremum theorem has
the strict quantifier order: resource-only positive `c,C,t0` precede every real
unit transverse illumination pair and every physical wavenumber and size.
It covers the boundary resource case `M=m`. The literal homogeneous error,
radius-choice and coefficient-interval certificates also compile, including
the explicit `mu=1,a=0.01` finite-sphere example.

Separate auxiliary modules identify the manuscript's opposite signed-wave
label convention, prove the exact static Hessian norm, and verify the displayed
Lorentz pole/loss/operating-frequency material properties. No dipole model or
scalar arithmetic certificate is substituted for an interacting continuum
response. The final combined quartic replay includes all 76 ingredient modules.

## Final verification and publication changes

All 23 original numbered statements have complete matching formal interfaces:
15 generalized propositions/lemmas/theorems/corollaries and eight quartic
theorems/lemmas. This includes clauses inside the statements, rather than just
their principal inequalities. The AI-assisted clause review is recorded in
[FORMALIZATION_SCOPE_REVIEW.md](FORMALIZATION_SCOPE_REVIEW.md) and its JSON companion.

| Project | Ingredient modules | Exact declaration inventory | Required public roots | Fresh replay |
|---|---:|---:|---:|---|
| Generalized research | 75 | 1,644 theorems, including generated helpers | 439 | Passed |
| Quartic Maxwell | 76 | 1,048 explicit public exports | 128; 20 physical core types pinned | Passed |

Generalized evidence is in `papers/generalized-research/formalization/verification/final-all-numbered/`;
quartic evidence is in `papers/quartic-maxwell/formalization/verification/report.json`
and its preserved `checkpoints/all-numbered-theorems-2026-10-15/` snapshot.
Six unchanged imported OQ7 roots used by the generalized correspondence have a
separate exact type/axiom audit bound to the final aggregate. All 13 generalized
controls and 12 quartic controls passed. The quartic rejection runner now accepts
portable `--lean-bin`; its previous runner and results remain preserved.

Fresh replay uses Lean's own kernel implementation. It does not constitute an
independently implemented checker, human peer review or a novelty assessment.
The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.
The unfinished superseded generalized runs are preserved under ignored `.local/`
and are not represented as successful publication evidence.

Only after both final replays passed, the current `arxiv/main.tex` files were
revised to describe their precise verified scope, pinned software and remaining
auxiliary limitations. Both bibliographies now cite the original Lean 4 and
Mathlib publications. The generalized finite-power beam proof now specifies the
normalized uniform disk aperture, unitary physical Fourier factor, square-root-two
field normalization, boundary flux cancellation and direct exact-target retuning.
The numbered manuscript theorem statements are unchanged. The new revision date
is 15 October 2026. Daniel Wang remains first and Junjie Zheng second, with the
same university affiliations and identically formatted clickable enduring emails.

Each paper now carries a portable `anc/lean-supplement.zip` inside its arXiv source
package. It includes exact proof sources, final records, dependency pins, the
unchanged shared source libraries, original target PDF/TXT, a hash checker and
public pinned-dependency restore instructions. TeX, compilers, Git metadata,
third-party caches and compiled Lean objects are excluded from the supplement.
The current source packages contain the TeX inputs and supporting ancillary
files, without the generated current manuscript PDF or TeX build auxiliaries.
Current paper/collection READMEs, reproduction instructions and submission
preparation now link the new proofs and distinguish historical reconstruction
records. Historical revision notes and audits remain unchanged.

[FORMALIZATION_MANUSCRIPT_BINDING.json](FORMALIZATION_MANUSCRIPT_BINDING.json)
links the frozen proof reports and their earlier reading versions to the revised
manuscript sources. [FORMALIZATION_PUBLICATION_VERIFICATION.json](FORMALIZATION_PUBLICATION_VERIFICATION.json)
records PDF/source/archive hashes, author metadata and mailto links, clean build
results, source/archive integrity checks and visual review of every rendered page.

- `quartic-maxwell`: 13 pages; resolved references, no overfull boxes, unchanged numbered statement blocks, matching source/archive hashes and both contact links checked.
- `generalized-research`: 17 pages; resolved references, no overfull boxes, unchanged numbered statement blocks, matching source/archive hashes and both contact links checked.

The full per-file list, including added/modified/deleted paths and before/after
SHA-256 values, is [FORMALIZATION_CHANGE_INVENTORY.json](FORMALIZATION_CHANGE_INVENTORY.json).
`SHA256SUMS` is refreshed while retaining its original ordering and newline format.
The inventory excludes itself and omits the checksum manifest's after-hash to
avoid circular hashes. Downloaded tools, caches and renders remain ignored.

Auxiliary exclusions remain explicit: generalized Remark 4.6 finite-cell
strictness, the full fixed-(T,a) optimizer phase/singular-spectrum classification,
some endpoint/dispersion discussions, and a separate global distributional beam
gluing theorem; quartic auxiliary matrix/Gram/translation refinements and empirical
or bibliographic claims. No claim that every sentence or display is formalized is
made. No arXiv upload, journal submission or external correspondence was performed;
the actual arXiv server build has not been tested.

The publication/navigation whitespace check passed. A complete staged diff check also identified 23 cosmetic trailing-space/final-blank-line diagnostics inside frozen proof sources, snapshots and compiler logs. These exact checked bytes are retained; the locations and decision are recorded in the publication verification JSON. No conflict-marker diagnostics were accepted.
