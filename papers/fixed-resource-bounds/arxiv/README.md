# Fixed-resource bounds: submission source

The current source is `main.tex` with `references.bib`. It uses ordinary LaTeX packages, has no external figures or data dependency, and compiles with pdfLaTeX and BibTeX without shell escape. The authors are Daniel Wang (McMaster University), followed by Junjie Zheng (Columbia University); both lasting contact addresses are hyperlinked in the manuscript. The manuscript date is 14 October 2026.

From this directory:

```text
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

Include `main.tex`, `references.bib` and the generated `main.bbl` in the submission source archive. The compiled PDF is a reading copy. Build logs and auxiliary files need not be included.

This is an editable reconstruction and professional revision of the preserved 22-page PDF, rather than a recovered original TeX file. [REVISION_NOTES.md](REVISION_NOTES.md) records the source hash, proof correspondence, corrections and omitted workflow/numerical material. The central ordinary proofs are included in the article; no Lean source or proof check was read, edited or executed for this revision. Uploading the manuscript and selecting a distribution license remain author actions.
