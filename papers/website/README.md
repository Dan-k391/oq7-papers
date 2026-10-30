# OQ7 paper website

Public directory: https://dan-k391.github.io/oq7-papers/

The `public/` directory contains complete HTML editions of the five current
`papers/<slug>/arxiv/` manuscripts, exact copies of their PDFs and source ZIPs,
and source/numbering manifests. The prescribed-extinction and fixed-resource manuscripts include
17 October scope clarifications distinguishing their single-frequency results
from the separately labeled broadband candidate extensions; the other manuscripts retain their own
release dates. The older `publication/manuscript/` HTML remains historical.
The geometry SVG is reused from that preserved publication snapshot.

Only `public/` is deployed to the `gh-pages` branch. Historical archives, local
work, credentials, and dependency caches are excluded. Two explicitly selected candidate research notes are released as supplements.
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
revision. The landing-page broadband section labels the boundary and strict-floor notes as
CANDIDATE proofs. These are two supplements to prescribed-extinction, not a sixth
paper, new formal verification, or independent human review.

The boundary candidate proposes X(center) = E* = min_B X, strict elsewhere on a
fixed positive band, with inf_B Gamma arbitrarily close to one in the unrestricted
two-layer reciprocal tensor class. It inherits the earlier Maxwell framework and
the strict-floor C0 aperture theorem. Caps are bandwise; no common geometry,
resource, linewidth, or positive material-loss floor is imposed.

The builder copies each original research-note.pdf byte-for-byte and creates a
deterministic source ZIP with an explicit allowlist: main.tex, STATUS.txt,
verification.json, the numerical script and results, and the two final compiler
logs. It records dependencies, candidate scope, filenames and hashes separately
under supplements in release-manifest.json. The verifier independently checks
those files, ZIP contents and scope labels. Original research sources, including
their historical publication-state statements, remain byte-for-byte preserved.
This candidate revision requires its own build, verification and deployment
record; the deployment record below applies only to the earlier scope revision.

## Historical 17 October scope deployment

The earlier 17 October scope revision was deployed to the public directory above. Source commit `22fed75636f16309ccd0fb471e8674d62d258dc5` supplied the static files deployed by `gh-pages` commit `d2568df53e2116d75890c5e15dc2755960b8eafc`. GitHub's Pages workflow succeeded, and all 24 served files matched the verified local release byte-for-byte. See [the dated deployment record](verification/deployment-2026-10-17.json); the earlier `verification/deployment.json` remains historical.

## Boundary candidate deployment

The labeled boundary candidate release is live at the public directory. Source commit `5dd4e1a6346c77232bf788ee87d6442d5f8614fc` supplied the verified static tree deployed by `gh-pages` commit `cfaa6c1b3833ea43203711d10ea6b0cf78b2d758`. GitHub Pages completed successfully. All 28 served files and the directory landing page matched the verified release byte-for-byte; `.nojekyll` is additionally present in the 29-file deployment tree. The live landing-page candidate label and links were also checked in the browser.

See [the candidate deployment record](verification/deployment-boundary-candidate-2026-10-17.json) and [the publication-format checks](verification/boundary-candidate-2026-10-17.json). These verify publication identity and format, not the mathematical validity of the candidate proof. Original research-stage status files remain historical evidence.

## Local editorial revision — 29 October 2026

The local static site was rebuilt from the five prose-edited manuscript sources, with exact-source auxiliary numbering and revised PDFs/source archives. See [the editorial report](../EDITORIAL_REVIEW_2026-10-29.md) and [the format verification](verification/editorial-2026-10-29.json). Historical proof correspondence remains bound to its earlier source versions. Deployment status is recorded separately from the format checks.

### Editorial website deployment

The editorial revision is live at the public directory. Source commit `3de356ceb9cb744a238f1cbd63a7bb836ea8bf44` supplied the verified static files deployed by `gh-pages` commit `6665bc235579a8137aae34cfa7c0bde451bd3c7f`. The GitHub Pages workflow succeeded; the live directory and all 28 served files matched the verified release byte for byte. See [the deployment record](verification/deployment-editorial-2026-10-29.json). This confirms publication identity, not the validity of mathematical claims.
