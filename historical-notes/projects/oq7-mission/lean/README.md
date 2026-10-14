# Independent OQ7 mission components

This project uses namespace `OQ7Mission`, Lean **4.34.1** (commit `5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. The copied `lake-manifest.json` retains all nine exact dependency revisions; its root package name is changed to `oq7Mission`. The original `outputs/oq7` proof sources and configuration are preserved.

The physical manuscript results remain **PARTIALLY FORMALIZED** by these components. Each successfully audited algebraic declaration has its actual hypotheses and kernel type exported; none is presented as a proof of the full Maxwell localization or compact cross-section theorems.

| Module | Proved content | Boundary |
|---|---|---|
| `Coercivity.lean` | Imaginary-part coercivity implies a lower norm bound; a positive uniform coercivity constant bounds current error by residual; residual `o(scale)` transfers to current error `o(scale)` | The coercivity inequality is an explicit hypothesis. No Maxwell operator, outgoing solution, solvability, or physical residual estimate is constructed. |
| `Observables.lean` | Bounded quadratic-work and incident-work continuity; current error `o(scale)` and explicit `O(scale)` current/incident bounds give work errors `o(scale^2)` and normalized convergence | Physical absorption positivity, operator identification, units, extinction normalization and optical-theorem identification with scattering remain obligations. No far-field operator bound is assumed or proved. |
| `RationalOverlap.lean` | Exact defined real 2×2 matrices, positivity/contraction, Lyapunov and complementary-slackness identities; a sharp **signed** objective upper bound and attainment for the specified rational SDP at `alpha=3/5`; a square-channel corollary | This is a finite-dimensional algebraic instance. It does not establish the global parameter-dependent Paper A Theorem 7.1, an absolute-value optical objective, or physical realizability. |

For the quadratic work, the quantitative inequality is

```
|Q_A(u) - Q_A(v)| <= ||A|| ||u-v|| (||u|| + ||v||).
```

For the incident work it is `|X_b(u)-X_b(v)| <= ||b|| ||u-v||`. These inequalities, rather than a radiation-map estimate, are what justify the normalized work convergence. Taking `scale=R` gives an algebraic `o(R^2)` work error. No physical residual or cross-section rate such as `R^(-14/15)` is claimed here.

## Reproduce the audit

The default Windows paths use the already installed portable Lean release and the preserved project's compiled dependency cache. From this directory:

```powershell
./bootstrap-cache.ps1
./verify.ps1 -Clean
```

The bootstrap creates only the new project's `.lake/packages` junction. It does not edit dependency source checkouts. The verifier cleans only `oq7Mission`, rebuilds the new library, checks all nine dependency revisions and tracked-source cleanliness, exports exact declaration types and proof/type dependency graphs, and audits every new kernel constant's transitive axioms. It checks all 83 original source/configuration hashes before and after.

Paths are parameters, so another checkout can use:

```powershell
./bootstrap-cache.ps1 -ExistingProject 'D:/research/outputs/oq7'
./verify.ps1 -Clean -PinnedBin 'D:/tools/lean-4.34.1-windows/bin' `
  -ExistingProject 'D:/research/outputs/oq7' -PythonExecutable 'D:/tools/python/python.exe'
```

The existing project's saved successful report and compiled `OQ7` library are inputs to the read-only theorem51 dependency export. On a fresh machine, install the exact Lean release, restore or build the original project with its own unchanged pinned sources/manifest, and fetch the exact nine dependency checkouts/cache before using the junction. Lake can fetch missing checkouts from the saved manifest; `lake exe cache get` in the original pinned project can obtain Mathlib's compatible compiled cache. The standalone original build instructions are in `../../oq7/README.md`. This project does not silently substitute another Lean release or Mathlib revision. Python 3 and Git are needed by the auditor; no third-party Python package is needed by the graph exporter.

## Evidence

`verification/report.json` records counts, hashes, exact pins and verification status. `build.log` and `clean.log` record the clean build. `statements.log` exports the actual complete kernel types, with explicit arguments, universes and coercions and notation disabled. `axioms.log` covers public declarations, private helpers, generated constants and definitions; only `propext`, `Classical.choice` and `Quot.sound` are allowed.

`dependencies.json` records direct type and proof/value constants for every new declaration and the recursive own-namespace closure. `theorem51-dependencies.json` does the corresponding recursive original `OQ7` traversal rooted at `OQ7.theorem51`.

`full-dependencies.json` additionally expands all named constants recursively, including imported Mathlib/Lean and private constants, for the eight generic results and the rational certificate, SDP upper bound, attainment and square corollary. `full-theorem51-dependencies.json` gives that full recursive expression closure for the original theorem51. Each file includes exact direct edges, per-root transitive constant lists and reachable axiom names. The method reads `ConstantInfo.type` and `value?(allowOpaque := true)` using `Expr.getUsedConstants`; kernel metadata which is not an expression is outside this graph. These are actual elaborated term dependencies, not names guessed from imports or source prose.

The separate `../integrity-tests` harness records successful rejection of false proofs, admitted proofs, transitive injected axioms and unused injected axioms. Its scratch modules are outside both proof libraries.

## Remaining physical obligations

The current-to-observable components require a concrete physical model to prove the outgoing Maxwell Green operator and domain, local singular/depolarization terms, the uniform imaginary-part coercivity inequality, existence and uniqueness of the solution, the truncation/commutator and grazing-mode residual estimates, and the required uniform current/incident/material-operator norm bounds. The absorption/extinction work identities with the selected cross-section normalization and a valid optical theorem must then connect the algebraic work quantities to physical absorption, extinction and scattering. Quantitative square-footprint exponents and the actual admissible material/geometry classes must be proved in that model. They are not inferred from these generic estimates.

The exact rational SDP result still needs the general parameter optimization and a separately proved map between optical channels and the SDP, including any absolute-value objective and realizability claim, before it could cover full Paper A Theorem 7.1. The existing independently verified scalar `OQ7.theorem51` is unaffected and has a different, exact scalar statement.
