# Finite-aperture and dipole manuscript revision

**Finite-Aperture Localization and Dipolar Bounds for Reciprocal Absorption Asymmetry**

Daniel Wang, McMaster University, `denialk391@gmail.com`; Junjie Zheng, Columbia University, `zjj2785@gmail.com`, in that order. Both contacts are clickable in the PDF using the common author format.

The current [PDF](paper.pdf) is generated from [reconstructed TeX](main.tex) and [references.bib](references.bib). [REVISION_NOTES.md](REVISION_NOTES.md) records the complete result mapping, scientific corrections and overlap with the stronger prescribed-extinction paper. The latter overlap matters when deciding whether to submit this as a separate article or companion material.

Upload [arxiv-source.zip](arxiv-source.zip), which contains compilation inputs only. Build from the repository root with `python scripts/build-arxiv.py compact-maxwell-cross-sections`; add `--tex-dir` for a non-PATH TeX Live installation. Scratch files stay under `.local/`, and shell escape is disabled. See [submission preparation](../../../ARXIV_SUBMISSION.md).
