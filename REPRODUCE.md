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

Existing complete replay logs are preserved in review-package/. Reorganization does not create a new independent-kernel check or certify the other papers. If a new fresh replay is requested, use the pinned version:

    lake env leanchecker --fresh --verbose PrescribedExtinction.PhysicalTheorem11

## Collection integrity and prior-work restoration

From the repository root:

    python scripts/verify-collection.py
    python scripts/restore-previous-work.py --prefix outputs/oq7 --destination .local/restored-scalar

The restoration tool validates paths and creates a new destination. It does not follow links, delete originals or restore excluded build/vendor caches. Historical projects retain their old scripts unchanged and may refer to former local paths; do not treat them as the active proof entry point.

## Local workspace environment

    .\scripts\enter-workspace.ps1

This adds the ignored local pinned Lean distribution to the current shell PATH only and selects the primary checkout. It does not install or upgrade global tools. The current chat's sandbox/task directory is not changed by cloning; open D:\\oq7-papers as a project for new Codex tasks.
