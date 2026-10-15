# Reproduction

The current editable inputs are `../arxiv/main.tex` and its bibliography. The files in `manuscript/` are exact publication snapshots.

From the repository root, check all package files, source identities and links:

```text
python scripts/sync-paper-packages.py --check --paper compact-maxwell-cross-sections
```

To rebuild the canonical PDF with the existing no-shell-escape TeX workflow and then refresh this package, run from `manuscript/`:

```text
python build.py --tex-dir PATH_TO_TEX_BIN
```

The wrapper calls the repository build script, then the package synchronizer. Synchronization verifies recorded build inputs and any existing proof/manuscript bindings before it writes. Manual changes to managed snapshot files are refused. The document check records reuse of the earlier PDF build and visual review; copying does not constitute a new mathematical verification or arXiv server build.

No paper-specific Lean source package is supplied. The correspondence table explicitly records that boundary; no companion proof is substituted.
