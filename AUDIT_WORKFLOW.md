# Paper audit workflow

This is the procedure used for the prescribed-extinction paper, condensed for re-use on any paper in `papers/`. Each audit lives in `papers/<paper>/audit-YYYY-MM-DD/`. Originals are never edited.

## Quick re-run

    git pull --ff-only
    python scripts/run-paper-audit.py papers/<paper>/audit-YYYY-MM-DD           # hashes, checks, Lean files
    python scripts/run-paper-audit.py papers/<paper>/audit-YYYY-MM-DD --kernel  # + leanchecker --fresh replays

The runner reads `audit.json` and writes `logs/` and `logs/last-run.json`. It exits nonzero on a hash mismatch, a failed check, a Lean error, `sorry`, or any axiom outside `propext`, `Classical.choice` and `Quot.sound`. Lean runs in the pinned build environment `papers/prescribed-extinction/formalization` (Lean 4.34.1, Mathlib `d13f23b7`), with the toolchain in `.local/toolchains/`. Override the toolchain with `LEAN_BIN`. Do not run `lake update`.

## Steps for a new audit

1. **Fix the target.** Record the path and SHA-256 of the exact PDF in `audit.json` and the README. Audit that file, not a later revision. Use a revision only as a reading aid and say so.
2. **Read the equations reliably.** Plain `pdftotext` and the stored `.txt` files list matrix entries column by column and drop square roots. Confirm every matrix and surd with layout mode: `pypdf … extract_text(extraction_mode="layout")`. If a rasterizer is available, look at the page image.
3. **Claim register.** List every theorem, lemma and proposition with its hypotheses, its dependencies, and what the paper says about its own status. Do not strengthen or weaken any statement.
4. **Three independent strands.** Work from definitions before reading earlier audits.
   - **A, analytic.** Re-derive each step: constants, kernels, limits, inverses, quantifier order.
   - **B, counterexamples and edge cases.** Look at degenerate parameters and excluded endpoints. Run adversarial random and hill-climb searches, and recompute any numerical tables with an independent method.
   - **C, model fidelity.** Check normalization, all radiation and polarization channels, reciprocity, passivity, and that both experiments use the same material.
5. **Checks.** Write scripts in `checks/` that use the standard library only, run with `python -I`, and write JSON results to `checks/results/`. Use exact `Fraction` arithmetic for certificates. Label float searches as diagnostics.
6. **Lean.**
   - **Existing declarations.** Before writing anything new, search the repository (`historical-notes/`, the OQ7 library, `archive/`) for existing declarations. Hash-compare their sources with the audited tag and replay them: `#check`, `#print axioms`, `leanchecker --fresh <Module>`. Compare the Lean statement with the manuscript, definition by definition.
   - **New modules.** Put new modules in `lean/`. Show at least one negative control: an admitted `sorry` must surface as `sorryAx`, and a wrong constant must fail.
7. **Classify each issue.** Use one of: fatal theorem failure; proof gap; missing assumption; correctable technical error; expository; verification-record error; unrecoverable evidence.
8. **Assign a status to each result.** Use one of: FULLY KERNEL VERIFIED; CONDITIONALLY VERIFIED; PARTIALLY FORMALIZED; ORDINARY PROOF ONLY; FAILED. Never equate AI agreement with human review, and never infer novelty from a proof.
9. **Priority.** Run a bounded search, list new leads, and leave priority unresolved unless the full sources are compared.
10. **Reconcile, then commit.** Compare the findings with earlier audits only after the independent strands. Write `README.md` (verdict and status table) and `MATHEMATICAL_AUDIT.md`. Commit the audit folder, its logs and any runner changes. Do not publish, submit or contact anyone without explicit authorization.

## Existing audits

- [Quartic Maxwell](papers/quartic-maxwell/audit-2026-10-14/README.md)
- [Generalized research](papers/generalized-research/audit-2026-10-14/README.md)
- Prescribed extinction: `papers/prescribed-extinction/review-package/` (sealed)
