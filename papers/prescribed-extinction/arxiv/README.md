# Prescribed-extinction arXiv source revision

**Unit Supremum of Absorption Asymmetry at Prescribed Extinction for Compact Reciprocal Dielectrics**

Daniel Wang — McMaster University — denialk391@gmail.com

Junjie Zheng — Columbia University — zjj2785@gmail.com

Manuscript date: 15 October 2026. The author order, affiliations and contact addresses are supplied author metadata; neither author is designated as corresponding author.

## Build

The manuscript uses ordinary TeX Live packages and an unchanged BibTeX bibliography. From this directory, run:

```text
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

The release PDF dated 15 October was actually built with Tectonic 0.17.0 (TeX bundle `6ffe055852f8faf66c0acbe1a7fb27f87b869a90bad1204f3bf4d9683f597c7c`), because the earlier local TeX Live installation was absent. The final build and a separate build from the source ZIP both ran offline, with shell escape disabled, and produced byte-identical PDFs. The ordinary PDFLaTeX recipe above remains the intended portable source-upload workflow; this finalization did not run PDFLaTeX or test the arXiv server.

To reproduce the recorded Tectonic PDF, set `SOURCE_DATE_EPOCH=1792065600`, `TECTONIC_CACHE_DIR` to a populated cache for that bundle, and `FONTCONFIG_FILE` to the absolute path of `verification/fonts.conf`. Create an empty `build/` directory and run:

```text
tectonic --only-cached --untrusted --keep-logs --keep-intermediates --outdir build main.tex
```

The minimal font configuration avoids a host-font configuration diagnostic; all manuscript fonts come from the TeX bundle. Compiler/cache files are obtained separately and are excluded from the release. Exact compiler identity, input hashes and logs are in `BUILD_VERIFICATION.json` and `verification/`.

The source and bibliography are ASCII. `figures/two-layer-geometry.pdf` is the only figure dependency. Include the generated `main.bbl` with the final source package; build logs and auxiliary files are not submission sources.

## Ancillary evidence

`anc/` contains byte-preserved copies of the frozen proof archive, statement correspondence, original verification manifest, final audit report/status, historical later checking record, and version/scope records. The proof ZIP contains no TeX, HTML, or compiled Lean-object members. It preserves the original mathematical source and recorded compiler/dependency pins; compiler binaries and dependency sources are obtained separately. No Git bundle is duplicated in this smaller package.

The exact audited declaration is `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement` at commit `686402a6c2d63820828729cc7ab02504632e3fe7`. Its frozen source ZIP SHA-256 is `d141a3ded8c2d9fe520c0c92ef82601f4e1b7ca3a5eb1580d018e33a8f4fd258`. Historical evidence records retain references to their originating package and should be read with their stated dates and scope.

The 14 October revision supplied author/contact/date metadata and portable ancillary filenames. The 15 October finalization adds a short Section 6 explanation of the absorber--waveplate mechanism and explains the fixed plate integer and contrast--thickness tradeoff. All theorem, lemma, proposition, proof and displayed-equation bodies and the bibliography remain unchanged from that release. See `CHANGES.md`, `FINALIZATION_VERIFICATION.json` and `SHA256SUMS` for the exact version, checks and file identities. It does not modify the earlier manuscript, frozen evidence, or formalization. The existing formal scope does not extend to every intermediate expository estimate, human peer review, an independently implemented checker, or scientific priority.
