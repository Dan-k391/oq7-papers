# OQ7 research verification mission

This directory contains an adversarial audit of the two manuscripts dated 10 October 2026, preserved original PDFs, three separately written AI-agent reviews, independent numerical experiments, and a new Lean component project. It accompanies the actual complete scalar project in `../oq7`. Original references and previous proof sources are unchanged.

Start with **VERIFICATION_REPORT.md** for the nine requested verdicts. Then use:

| Artifact | Purpose |
|---|---|
| `MATHEMATICAL_AUDIT.md` | Exact classes, theorem ledger, mathematical dependency graph, reconciled issues and evidence limits |
| `MAXWELL_LOCALIZATION_AUDIT.md` | Detailed reconstruction of every analytical bridge in B3.1 and the square rate |
| `LEAN_STATUS.md` | Exact formal coverage, declarations, build/axiom evidence and remaining obligations |
| `NOVELTY_REVIEW.md` | Primary-source equivalence comparisons and unresolved access/priority questions |
| `MANUSCRIPT_STATUS_ADDENDUM.md` | Current source availability and formal-status corrections; original PDFs stay unchanged |
| `audits/` | Separate analytical, counterexample, model-fidelity and source-inventory records |
| `numerics/` | Independently authored exact/symbolic/high-precision/finite-model calculations and complete results |
| `lean/` | New pinned generic estimates and exact rational matrix optimization, with actual compilation/census evidence |
| `integrity-tests/` | Deliberately bad isolated fixtures and logs demonstrating rejection of false/admitted/axiomatic proofs |
| `reference_manifest.json` | Original paths, page counts and unchanged reference hashes |
| `MISSION.md` | The complete original user request |

The exact scalar Theorem 5.1 is fully kernel verified. The complete general overlap theorem and the actual compact three-dimensional Maxwell results are not fully formalized. Their ordinary proofs survived the audit; mathematical support, formal verification and novelty are separate assessments.

## Reproduction

The complete distribution archive places this directory at `oq7-mission/` and the preserved older physical project at `scalar-lean/`. On the original PC the older project is `../oq7/`. Its clean build was completed in the preceding continuation and its source hashes, exact theorem type and axiom inventory were independently rechecked in this mission. Follow its pinned-toolchain setup instructions; the command is:

```powershell
Set-Location <physical-project-directory>
.\verify.ps1 -Clean -Milestone theorem51-independent
```

For the new component project, use the exact clean build/verification command documented in `LEAN_STATUS.md` and `lean/README.md`. The package excludes compiler binaries, dependency caches and compiled modules. It includes the toolchain and complete dependency manifest. The existing local cache junction is a machine-local convenience; a clean installation must resolve the pinned dependencies and official Lean release itself.

Run the independent numerical program with Python 3.12 and the exact observed dependency versions in `numerics/requirements.txt`:

```powershell
python numerics/audit_b_checks.py
```

The full run includes seven dense DDA solves. The `--lightweight` option omits them and overwrites the same result file; copy the saved full results elsewhere before using that option if preserving them matters. This is a finite-model experiment, not a continuum error certificate. The manuscript's large author FFT/GMRES runs were not reproduced.

For the negative-control harness, see `integrity-tests/README.md`; its original-project path can be supplied explicitly when extracted elsewhere. Deliberately bad fixtures are outside both proof libraries and do not enter their accepted theorem inventories.

`scripts/package_and_check.py` validates required artifacts, old source hashes, unchanged PDFs, numerical check outcomes, then creates and verifies the distribution ZIP. `DELIVERY_CHECKS.json` records those checks and the archive hash. A clean full new-project build and theorem audit must be completed before packaging.
