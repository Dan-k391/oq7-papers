# Reproduce and work in the collection

Primary clone: D:\\oq7-papers. Repository: https://github.com/Dan-k391/oq7-papers.

## Current prescribed-extinction manuscript

The current arXiv source revisions and clean upload ZIPs are documented in [ARXIV_SUBMISSION.md](ARXIV_SUBMISSION.md). Build them with `scripts/build-arxiv.py`; local intermediates stay in `.local/`. The workflow compiles manuscripts only and does not run proof code.

The named manuscript and its existing generation record are in papers/prescribed-extinction/publication/. From its manuscript/ directory, run build.py with the installed XeLaTeX/BibTeX/Pandoc or Tectonic/Pandoc executable arguments documented in the unchanged publication/REPRODUCE.md. Do not overwrite the earlier review or frozen PDFs.

## Final audited proof

Use exact Lean 4.34.1, compiler commit 5045d0056413266e57c625dcd7c365b10e377c52. Mathlib is d13f23b723b8a846827a245b89c10fc7d3f11612; all nine pins are supplied in the dependency snapshots. No upgrade is needed.

From papers/prescribed-extinction/formalization/:

    python configure.py
    python restore-dependencies.py --archives-directory ../review-package/release/dependency-sources
    lake build OQ7 PrescribedExtinction
    lake env lean verification/FinalCompleteTheorem.lean
    python run-audit.py

The restorer is for a new checkout with no dependency directories. A compatible cache must have exactly those pinned revisions. Do not run lake update. The pinned compiler is a member of the complete private archive listed in shared/ASSET_REGISTRY.json; large tool/runtime files live in ignored .local/toolchains/, not ordinary Git source.

Existing complete prescribed-extinction replay logs are preserved in review-package/. Those historical records do not certify the other papers; the quartic and generalized projects below have their own checks. If a new fresh replay is requested, use the pinned version:

    lake env leanchecker --fresh --verbose PrescribedExtinction.PhysicalTheorem11

## Quartic and generalized formalizations

Both use the same unchanged Lean/Mathlib pins above. Their current arXiv source ZIPs contain `anc/lean-supplement.zip`, which can be reproduced without access to the private repository. Extract a supplement into an empty directory, run `python verify_supplement.py`, and follow its root README to restore the nine exact public dependency commits and build `OQ7 PrescribedExtinction`. The supplement excludes caches, tool binaries and TeX. Do not run `lake update`.

After restoring those libraries, run the quartic verifier from its `formalization/` directory, supplying the absolute pinned toolchain bin directory:

```text
python verify.py --lean-bin PATH_TO_PINNED_LEAN_BIN --fresh-kernel
```

For generalized research use its default fresh replay and preserve the included final record by choosing a new output directory:

```text
python verify.py --lean-bin PATH_TO_PINNED_LEAN_BIN --output-dir verification/new-run
```

Read [quartic scope](papers/quartic-maxwell/formalization/README.md) and [generalized scope](papers/generalized-research/formalization/README.md) for the exact statements, isolated expected-failure controls and remaining auxiliary obligations. Compilation, exhaustive type/axiom inventories and fresh replay are separate recorded stages. Fresh replay uses Lean's own kernel implementation; it is not an independently implemented checker or human review.

## Collection integrity and prior-work restoration

From the repository root:

    python scripts/verify-collection.py
    python scripts/restore-previous-work.py --prefix outputs/oq7 --destination .local/restored-scalar

The restoration tool validates paths and creates a new destination. It does not follow links, delete originals or restore excluded build/vendor caches. Historical projects retain their old scripts unchanged and may refer to former local paths; do not treat them as the active proof entry point.

## Local workspace environment

    .\scripts\enter-workspace.ps1

This adds the ignored local pinned Lean distribution to the current shell PATH only and selects the primary checkout. It does not install or upgrade global tools. The current chat's sandbox/task directory is not changed by cloning; open D:\\oq7-papers as a project for new Codex tasks.

## Matching companion-paper packages

Quartic Maxwell, generalized research, fixed-resource bounds and compact Maxwell cross sections have the same publication/supplement/review entry points as prescribed-extinction. Their editable sources remain in `arxiv/`; `publication/manuscript/` contains exact snapshots.

```text
python scripts/sync-paper-packages.py --preflight
python scripts/sync-paper-packages.py --check
python scripts/sync-paper-packages.py --sync --paper quartic-maxwell
```

`--sync` verifies source/build identities and existing proof/manuscript bindings before copying, and refuses to overwrite manually changed managed files. Each publication manuscript has a `build.py` wrapper for the canonical TeX build followed by synchronization. Refresh revision inventories and repository checksums before committing changed outputs. The S1–S4 indexes distinguish actual proof archives from status-only records; no companion theorem is automatically transferred to another paper. Package identity checks reuse the existing mathematical verification and are not new theorem checks. See [the structure change record](PACKAGE_STRUCTURE_CHANGES.md).
