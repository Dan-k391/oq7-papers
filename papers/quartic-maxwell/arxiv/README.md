# Uniform Quartic Bounds for Reciprocal Absorption–Scattering Asymmetry

Daniel Wang, McMaster University, `denialk391@gmail.com`; Junjie Zheng, Columbia University, `zjj2785@gmail.com`, in that order. Both PDF contacts use the same clickable mailto format.

The [13-page PDF](paper.pdf) is generated from [reconstructed TeX](main.tex) and [references.bib](references.bib). The [source upload ZIP](arxiv-source.zip) contains the TeX compilation inputs and a [Lean source supplement under anc/](anc/README.md). The supplement carries exact proof sources, dependency pins and final verification records; compiler binaries and build caches are excluded.

The [formalization change record](../../../FORMALIZATION_CHANGES.md), [manuscript-version binding](../../../FORMALIZATION_MANUSCRIPT_BINDING.json) and [publication verification record](../../../FORMALIZATION_PUBLICATION_VERIFICATION.json) describe this revision. [REVISION_NOTES.md](REVISION_NOTES.md) records the complete claim disposition and original PDF hashes. Those revision notes describe the earlier reconstruction and remain unchanged as historical evidence.

Build from the repository root with `python scripts/build-arxiv.py quartic-maxwell`; use `--tex-dir` for a non-PATH TeX Live installation. The build disables shell escape and writes scratch files under `.local/`. It compiles the manuscript; the separate [Lean verifier](../formalization/README.md) checks proofs. See the collection's [submission instructions](../../../ARXIV_SUBMISSION.md). No submission has been made.
