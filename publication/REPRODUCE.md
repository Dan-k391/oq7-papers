# Reproduction

## Manuscript

The manuscript sources are `manuscript/main.tex`, `manuscript/references.bib`, and the vector assets in `manuscript/figures/`. The PDF and HTML are generated from these sources; the HTML uses native MathML and TeX-generated equation, theorem, section, and citation numbers.

From `manuscript/`, build with XeLaTeX, BibTeX, and Pandoc:

```text
python build.py --xelatex PATH_TO_XELATEX --bibtex PATH_TO_BIBTEX --pandoc PATH_TO_PANDOC
```

Alternatively, use Tectonic and Pandoc:

```text
python build.py --tectonic PATH_TO_TECTONIC --pandoc PATH_TO_PANDOC
```

Pandoc 3.12.1 is the documented conversion version. The earlier review build used Tectonic 0.17.0; the publication revision uses the XeLaTeX/BibTeX route. Executables are installed separately. Its build and document checks are recorded in [CHANGES.md](CHANGES.md).

## Frozen proof source

The [source ZIP](manuscript/reproducibility/OQ7-complete-physical-theorem11-source.zip) and [Git bundle](manuscript/reproducibility/OQ7-complete-physical-theorem11.bundle) preserve audited commit `686402a6c2d63820828729cc7ab02504632e3fe7`. Their SHA-256 identities are recorded in the accompanying [frozen manifest](manuscript/reproducibility/manifest.json). The archive includes the proof sources and their historical checking records. It does not bundle the compiler or dependency sources.

Use Git, Python 3, and [Lean 4.34.1](https://github.com/leanprover/lean4/releases/tag/v4.34.1), compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`. The pinned Mathlib revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`; all dependency revisions are recorded in the extracted `sources/pinned-lake-manifest.json`.

Verify the archive identity, extract it into a new directory, activate the pinned Lean toolchain, and run the following commands from the extracted source root:

```text
lean --version
python configure.py
lake build OQ7 PrescribedExtinction
lake env lean verification/FinalCompleteTheorem.lean
```

`configure.py` replaces the archived machine-specific package path with `.lake/packages` and restores the locked manifest. Run it before Lake. Lake fetches the pinned dependencies when they are absent; network access is required for those downloads. Do not run `lake update` or substitute newer revisions. The build can compile dependency objects from source; a compatible Mathlib cache for the same pins is optional.

For an additional empty-environment replay using Lean's own kernel implementation:

```text
lake env leanchecker --fresh --verbose PrescribedExtinction
```

This is same-kernel replay, not an independently implemented checker. The [audit provenance](manuscript/reproducibility/AUDIT_PROVENANCE.md) distinguishes the frozen build, completed AI-assisted main-statement review, and historical later checking records. Rebuilding the proof does not establish scientific priority or certify every paragraph of the manuscript's expository proof.
