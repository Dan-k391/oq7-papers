# Fixed-resource bounds: submission source

The current source is `main.tex` with `references.bib`. It uses ordinary LaTeX packages, has no external figures or data dependency, and compiles with pdfLaTeX and BibTeX without shell escape. The authors are Daniel Wang (McMaster University), followed by Junjie Zheng (Columbia University); both lasting contact addresses are hyperlinked in the manuscript. The manuscript date is 17 October 2026.

From this directory:

```text
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

Include `main.tex`, `references.bib` and the generated `main.bbl` in the submission source archive. The compiled PDF is a reading copy. Build logs and auxiliary files need not be included.

This is an editable reconstruction and professional revision of the preserved 22-page PDF, rather than a recovered original TeX file. [REVISION_NOTES.md](REVISION_NOTES.md) records the source hash, proof correspondence, corrections and omitted workflow/numerical material. The central ordinary proofs are included in the article; no Lean source or proof check was read, edited or executed for this revision. Uploading the manuscript and selecting a distribution license remain author actions.

## 17 October scope revision

The “Other channels, backgrounds and bandwidth” paragraph now explains that the existing pointwise fixed-resource gaps already give band ceilings, while additional causal frequency coupling and joint realizability remain unresolved. Existing theorem/proof bodies, displays and bibliography are preserved. No new proof audit is claimed. See [the scope change note](../../../BROADBAND_SCOPE_CHANGES_2026-10-17.md).

This revision uses Tectonic 0.17.0 with pinned TeX bundle `6ffe055852f8faf66c0acbe1a7fb27f87b869a90bad1204f3bf4d9683f597c7c`. To reproduce its offline build, set `SOURCE_DATE_EPOCH=1792238400`, `TECTONIC_CACHE_DIR` to a populated cache for that bundle, and `FONTCONFIG_FILE` to the absolute path of `verification/scope-2026-10-17/fonts.conf`. Create an empty `build/` directory and run:

```text
tectonic --only-cached --untrusted --keep-logs --keep-intermediates --outdir build main.tex
```

The revision-specific build record is `BROADBAND_SCOPE_VERIFICATION_2026-10-17.json`, with logs under `verification/scope-2026-10-17/`; consult that record for actual checks and results. The preserved `BUILD_VERIFICATION.json` applies only to its historical release. This reproduction recipe does not establish a PDFLaTeX or arXiv-server test.