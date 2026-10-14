# Prescribed-extinction arXiv source revision

**Unit Supremum of Absorption Asymmetry at Prescribed Extinction for Compact Reciprocal Dielectrics**

Daniel Wang — McMaster University — denialk391@gmail.com

Junjie Zheng — Columbia University — zjj2785@gmail.com

Manuscript date: 14 October 2026. The author order, affiliations and contact addresses are supplied author metadata; neither author is designated as corresponding author.

## Build

The manuscript uses ordinary TeX Live packages and an unchanged BibTeX bibliography. From this directory, run:

```text
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

The source and bibliography are ASCII. `figures/two-layer-geometry.pdf` is the only figure dependency. Include the generated `main.bbl` with the final source package; build logs and auxiliary files are not submission sources.

## Ancillary evidence

`anc/` contains byte-preserved copies of the frozen proof archive, statement correspondence, original verification manifest, final audit report/status, historical later checking record, and version/scope records. The proof ZIP contains no TeX, HTML, or compiled Lean-object members. It preserves the original mathematical source and recorded compiler/dependency pins; compiler binaries and dependency sources are obtained separately. No Git bundle is duplicated in this smaller package.

The exact audited declaration is `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement` at commit `686402a6c2d63820828729cc7ab02504632e3fe7`. Its frozen source ZIP SHA-256 is `d141a3ded8c2d9fe520c0c92ef82601f4e1b7ca3a5eb1580d018e33a8f4fd258`. Historical evidence records retain references to their originating package and should be read with their stated dates and scope.

This revision changes author/contact/date metadata and replaces package-relative PDF supplement hyperlinks with plain ancillary filenames. It preserves all theorem, lemma, proposition, proof and equation bodies and the bibliography from the existing named publication source. It does not modify the earlier manuscript, frozen evidence, or formalization. The existing formal scope does not extend to every intermediate expository estimate, human peer review, an independently implemented checker, or scientific priority.
