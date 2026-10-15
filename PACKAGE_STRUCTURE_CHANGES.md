# Paper package structure changes — 15 October 2026

Baseline: `02d1388`. The four companion papers now use the same core folder roles
as prescribed-extinction. This revision concerns folder/package structure only.

```text
papers/<paper>/
  arxiv/                         editable canonical manuscript and source upload
  formalization/                 own checked project or explicit status-only entry
  publication/
    AUTHOR_INFORMATION.md
    README.md, REPRODUCE.md, CHANGES.md
    CHANGE_INVENTORY.json, SHA256SUMS, SOURCE_CHANGES.diff
    manuscript/
      main.tex, references.bib, main.bbl, paper.pdf, build.py
      theorem-correspondence.csv, theorem-correspondence.html
      reproducibility/           S1–S4 index, provenance, scope and evidence
    verification/                document/build records and package manifest
  review-package/                historical evidence index and version dispositions
```

Applied to quartic Maxwell, generalized research, fixed-resource bounds and
compact Maxwell cross sections. Existing historical manuscript and audit
directories remain at their original locations; the review-package entry points
link them without moving or rewriting their contents. No new sealed review
release or human referee approval is implied.

The manuscript PDFs, TeX, bibliographies, author order, contacts, dates, layout,
section structure and mathematical text are unchanged. Publication manuscripts
are byte-identical snapshots of the canonical arxiv files. No duplicate editable
source is established. The prescribed-extinction package is entirely unchanged.

Quartic and generalized supplements contain byte-preserved copies of their own
existing proof archive, final report, coverage ledger and manuscript binding.
Fixed-resource and compact-Maxwell have explicit status-only formalization
directories: no paper-specific Lean project, source archive or formal verification
is invented. Their correspondence tables inventory current source labels.

Added `scripts/sync-paper-packages.py` for preflight, safe synchronization and
read-only checking. All four canonical build records and existing relevant proof
source/report hashes must pass before synchronization writes. The checker verifies
canonical-copy equality, provenance/checksums and local links. The rebuild wrappers
use the existing no-shell-escape manuscript workflow. Managed manual changes are
refused; historical files and existing formalizations are never overwritten.

S1 contains scope-aware correspondence; S2 links actual paper-specific source
evidence where supplied; S3 gives the existing verification/build identities;
S4 records provenance and version boundaries. No absent figure, HTML manuscript,
Git history bundle or proof certificate is fabricated merely to match filenames.

Current paper READMEs and collection reproduction/navigation are updated only
after package checks succeed. Prior mathematical verification is reused for its
exact source version; no Lean proof or PDF rendering is rerun for a byte copy.

Final checks and the complete per-file before/after inventory are recorded in
[PACKAGE_STRUCTURE_VERIFICATION.json](PACKAGE_STRUCTURE_VERIFICATION.json) and
[PACKAGE_STRUCTURE_CHANGE_INVENTORY.json](PACKAGE_STRUCTURE_CHANGE_INVENTORY.json).
The repository checksum manifest retains its original order and newline format.
No arXiv upload, journal submission or external correspondence is performed.

Final results: all four package checks passed, including 160 local links, canonical snapshot/provenance equality and publication checksums. A second synchronization wrote zero files. Separate temporary negative controls confirmed tampered snapshots are detected and manual edits are not overwritten. All 1,327 tracked prescribed-extinction/current arXiv/original manuscript and audit files selected by the preservation check remain byte-identical to the baseline.
