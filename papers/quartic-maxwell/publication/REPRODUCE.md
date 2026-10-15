# Reproduction

The current editable inputs are `../arxiv/main.tex` and its bibliography. The files in `manuscript/` are exact publication snapshots.

From the repository root, check all package files, source identities and links:

```text
python scripts/sync-paper-packages.py --check --paper quartic-maxwell
```

To rebuild the canonical PDF with the existing no-shell-escape TeX workflow and then refresh this package, run from `manuscript/`:

```text
python build.py --tex-dir PATH_TO_TEX_BIN
```

The wrapper calls the repository build script, then the package synchronizer. Synchronization verifies recorded build inputs and any existing proof/manuscript bindings before it writes. Manual changes to managed snapshot files are refused. The document check records reuse of the earlier PDF build and visual review; copying does not constitute a new mathematical verification or arXiv server build.

For proofs, extract `manuscript/reproducibility/lean-source.zip` to an empty directory, run its `verify_supplement.py`, and follow its root README for exact dependency pins and fresh replay. Compiler/dependency caches remain external. Fresh replay uses Lean's own kernel implementation.
