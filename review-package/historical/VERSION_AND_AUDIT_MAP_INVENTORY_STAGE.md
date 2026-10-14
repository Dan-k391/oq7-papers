# OQ7 version and audit map

Authorized root: `C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1`. Exact final commit recovered: `686402a6c2d63820828729cc7ab02504632e3fe7`, tree `580737ccf6557102d601894145cc0229ae1f83e3`.
The frozen archive and original tracked working files were compared byte-for-byte by SHA-256 with every commit blob. Disagreements: 0. Full identities are in COMMIT_FILE_IDENTITIES.json.

## Separate version families

| Family | Evidence and content identity | Actual scope / disposition |
|---|---|---|
| Old uncompiled scalar-thickness checkpoint | `outputs/oq7/sources/original-checkpoint.md`, SHA-256 `e142284fb1d2800f6a7e2c5346200b924435dded5e6b7793f5b2a4d7c1ee64f1` | Header explicitly says blocked before kernel verification, not a compiled Lean project. Target: scalar finite multilayer thickness asymptotic at fixed loss mass, transmitted power and mean absorptance. |
| Older 43-authored-theorem finite-port Lean supplement | Historical references describe a distinct Lean 4.19.0 supplement. No corresponding source/build package was recovered in the scanned root or archives. | **not recovered**. It is not the 692-theorem scalar project, 35-theorem mission components, or the final Maxwell repository. Historical reports are not source recovery. |
| Later completed scalar package | `outputs/oq7`; `outputs/OQ7_Lean_verified.zip`, SHA-256 `0cf6849573f2d24992ae5d12359beb4bce4dc2a9bb4d3309d13904fce91cfe5b`; saved inventory describes 77 modules, 692 authored theorems, 1288 kernel theorem constants | Separate one-dimensional scalar formalization, principal declaration `OQ7.theorem51`. Not substituted for the Maxwell theorem; not rebuilt by this audit. Counts are preserved evidence, not regenerated here. |
| Intermediate mission components | `outputs/oq7-mission/lean/verification/report.json` records 35 authored theorems; separate coercivity/work/rational SDP components | Explicitly partial physical coverage. Not the 43-theorem supplement or final Maxwell proof. |
| Claimed new full-Maxwell formalization | `outputs/oq7-prescribed-extinction` at `686402a6c2d63820828729cc7ab02504632e3fe7`; `PrescribedExtinction/PhysicalTheorem11.lean`, SHA-256 `656353efe23d729d63e17110540f52997dd4bacbeb607610b9853e3cad9ca180` | Exact requested source recovered. Principal declaration `OQ7Prescribed.theorem11_complete : PhysicalTheorem11Statement`. Fresh reproduction pending at this inventory stage. |

## Manuscript identities

| Version | SHA-256 | Pages / role |
|---|---|---|
| Primary `outputs/oq7-paper1-publication/paper.pdf` | `aa3a3fdb569a69d9fef82ecd54fe94d346f3723a0e65f597c24ac18ee3e1890d` | 16 pages; exact requested title; identical to `build/main.pdf` |
| Pre-minor preserved PDF | `25707ace339ac54cc4dfdb9f2f7711cf3ba6b2ca55193afd77c5b18169551647` | 16 pages; different content |
| Pre-correction preserved PDF | `1b925cada9f78cbe0380bd5aa0ffd5923d60551127cfeb3bb77d2978b8d2f528` | 15 pages; different content |
| Frozen repository scientific specification | `3d9775d849234e828370d7c96d8bdcdd574beb6831a7906ea6b7706579868710` | 19 pages; original Theorem 1.1 authority at baseline audit; not the current 16-page publication PDF |
| Old scalar note | `f0d553b936d584c6a518bd21fd59385909556ddcb43af9f97c739edf119e3ad6` | 18 pages; distinct scalar-thickness theorem |

PDF_VERSION_INVENTORY.json includes all direct and archived PDF instances. Version labels above are backed by hashes and extracted contents, not timestamps alone.

## S1-S4 recovered

- S1: `outputs/oq7-paper1-publication/theorem-correspondence.csv` and `.html`.
- S2: `outputs/oq7-paper1-publication/reproducibility/OQ7-complete-physical-theorem11-source.zip` and `.bundle`. Hashes: `d141a3ded8c2d9fe520c0c92ef82601f4e1b7ca3a5eb1580d018e33a8f4fd258` and `5a4e3a4623a910ee1f5993bc43b10da38d70125ef4aa74a22653b540b2db8479`. Each is byte-identical to its counterpart in `outputs/oq7-physical-theorem11-review-686402a6c2d6`.
- S3: `reproducibility/manifest.json`, SHA-256 `08aa0bd878602a9d112cf7d98d9bd7d22f9ae31c014f88a14396a292f18ec6a5`, and verification logs/reports inside S2. Their claims are historical until independently reproduced.
- S4: `reproducibility/AUDIT_PROVENANCE.md`, SHA-256 `d6e8c40466eb90733bb48cc4a24bdf6da2304ad05d042f4d46aca9ab7959f26a`. It identifies the older audit and unavailable named final report.

## Reviews and actual examined identities

| Review | Actual examined identity | Scope and limits |
|---|---|---|
| `verification/claude-independent-audit-5a8350d.md`, SHA-256 `50d854e335d44cdf1d5a3710f3bc542a4a1a6c28593a46cd320a2ea6ed9f7245` | `5a8350d5408c38e333c9f6b6d8a94816c794120b`, tree `a1b03d72e958851f2418f97a6b5c40c0689e305c`; declaration `OQ7Prescribed.theorem11` | Kernel PASS, semantic fidelity FAIL, mathematical completeness FAIL for the existence-only baseline. Not a review of the final commit. |
| `oq7-paper1-publication/PUBLICATION_ISSUES.md` | Explicit source inspection of frozen `686402a6c2d63820828729cc7ab02504632e3fe7`; original manuscript `1e2e948a...` / PDF `1b925cad...`; later minor correction notes | AI-assisted publication/source correspondence review. Reports no confirmed P0 error and missing later independent review. It did not run a new complete replay. |
| `oq7-paper1-publication/MATHEMATICAL_CONSISTENCY.md`, SHA-256 `1afbd38cd52bfce643988b9636cf30a923bd481bfee0e5c01772ef4f39aef8c1` | Final manuscript LaTeX `db316052e8d93d379696b6d4fa392b51adad35fa23ae05739fb60a5380729884`, PDF `aa3a3fdb569a69d9fef82ecd54fe94d346f3723a0e65f597c24ac18ee3e1890d`; uses frozen final definitions | Focused mathematical checks of corrections; not a comprehensive independent final-commit semantic audit or human certification. |
| `oq7-mission/NOVELTY_REVIEW.md` | 41-page Paper A `3f01036f...` and 24-page Paper B `eb85dd06...` | Earlier priority/equivalence review of different manuscripts. It does not establish priority for the current prescribed-extinction theorem. |
| `OQ7_Final_Lean_Audit_686402a6.txt` or equivalent substantive final independent audit | No review body recovered | **not recovered**. The manifest and review prompt are not a completed review. |

The source and archive scans read 7760 text items and 27 PDF instances without reported extraction errors; nested archive identities are recorded. Searches stayed inside the corrected root and did not follow either dependency junction. No Downloads or other project location was searched in this audit. Historical S4 descriptions of wider searches are evidence about earlier work, not this audit's authorization.
