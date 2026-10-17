# OQ7 paper website

Public directory: https://dan-k391.github.io/oq7-papers/

The `public/` directory contains complete HTML editions of the five current
`papers/<slug>/arxiv/` manuscripts, exact copies of their PDFs and source ZIPs,
and source/numbering manifests. The prescribed-extinction and fixed-resource manuscripts include
17 October scope clarifications distinguishing their single-frequency results
from proposed broadband extensions; the other manuscripts retain their own
release dates. The older `publication/manuscript/` HTML remains historical.
The geometry SVG is reused from that preserved publication snapshot.

Only `public/` is deployed to the `gh-pages` branch. Historical archives, local
work, new closure notes, credentials, and dependency caches are excluded.
GitHub Pages serves the branch root; `.nojekyll` makes this a plain static site.
No remote scripts, fonts, accounts, analytics, or paid services are needed.

## Rebuild

Use Python 3, Pandoc 3.12.1, and Tectonic 0.17.0 with the project's existing
pinned TeX bundle cache. Keep compiler tools and caches in `.local/`. From the
repository root (replace the two executable/cache paths with local paths):

```powershell
python papers/website/prepare_aux.py --tectonic <tectonic.exe> --cache <cache-directory> --output .local/pages-rebuild
python papers/website/build_pages.py --pandoc <pandoc.exe> --aux-root .local/pages-rebuild
python papers/website/verify_site.py --aux-root .local/pages-rebuild --report .local/pages-rebuild/verification.json
python -m http.server 8769 --bind 127.0.0.1 --directory papers/website/public
```

The auxiliary build copies compilation inputs into a fresh scratch directory;
it never edits the current paper sources or PDFs. Math and scientific prose come
from the LaTeX. Section, theorem, equation, and citation numbers are checked
against fresh exact-source AUX/BBL outputs. Legacy math font declarations and
macro-expanded derivative braces receive equivalent MathML-compatible spelling.
Numbered `align` rows retain their individual numbers and link targets.

The independent verifier checks release identity, ZIP manuscript identity,
headings, statement and equation inventories, bibliography/citations, local
links and fragments, duplicate IDs, unresolved markers, and runtime resources.
All Pandoc conversion warnings fail the build.

## Release scope

The historical 15 October 2026 edition passed publication-format checks for six HTML pages,
223 numbered equations, 47 statement environments, and 82 references. The
website preserves the scientific qualifications in each manuscript. This is a
publication-format and deployment record, not a new proof audit, novelty claim,
human peer review, or a declaration that every interpretation of OQ7 is solved.

See `verification/` for the exact build/format records and `public/release-manifest.json`
for the published input and output hashes. Preserve older paper and audit records.

The release manifest derives its edition date from the latest manuscript date
and records each paper's individual date and hashes. New builds require their
own verification report; the historical counts above do not certify a later
revision. The landing-page broadband section describes proposed research,
not a sixth paper or a verified broadband result.
## 17 October deployment

The 17 October scope revision is live at the public directory above. Source commit `22fed75636f16309ccd0fb471e8674d62d258dc5` supplied the static files deployed by `gh-pages` commit `d2568df53e2116d75890c5e15dc2755960b8eafc`. GitHub's Pages workflow succeeded, and all 24 served files matched the verified local release byte-for-byte. See [the dated deployment record](verification/deployment-2026-10-17.json); the earlier `verification/deployment.json` remains historical.
