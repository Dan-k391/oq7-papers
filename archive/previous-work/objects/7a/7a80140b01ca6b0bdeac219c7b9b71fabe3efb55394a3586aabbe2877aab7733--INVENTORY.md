# OQ7 inventory

Initial inventory generated before reproduction. Recovery: exact final repository recovered.

Authorized root: `C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1`.

Repository `outputs/oq7-prescribed-extinction` has observed HEAD `686402a6c2d63820828729cc7ab02504632e3fe7`. A detached disposable checkout was recovered from the frozen bundle. Original working tree preserved.

All 6196 direct regular files were SHA-256 hashed. SOURCE_FILE_HASHES.csv records exact absolute paths, sizes, hashes, and attributes, including hidden/ignored files. ARCHIVE_MEMBER_HASHES.csv inventories archive members, including nested ZIPs. PDF_VERSION_INVENTORY.json distinguishes PDFs by content hashes and page counts. No source junction was followed; both skipped junctions are listed below.

| Artifact path relative to authorized root | SHA-256 | Purpose / commit attribution |
|---|---|---|
| `outputs/oq7-paper1-publication/paper.pdf` | aa3a3fdb569a69d9fef82ecd54fe94d346f3723a0e65f597c24ac18ee3e1890d | Primary 16-page manuscript |
| `outputs/oq7-paper1-publication/main.tex` | db316052e8d93d379696b6d4fa392b51adad35fa23ae05739fb60a5380729884 | Primary manuscript source |
| `outputs/oq7-paper1-publication/theorem-correspondence.csv` | ee7515f7969d4389361b9eeb3f220545a222bc3db2d7205e011f2c4875bc82ff | S1 theorem correspondence |
| `outputs/oq7-paper1-publication/theorem-correspondence.html` | 4783659a6c2d1371a0cd5bcdd6faee98c9cf669a528a5e15d0cbd1582dca5d40 | S1 readable correspondence |
| `outputs/oq7-paper1-publication/reproducibility/OQ7-complete-physical-theorem11-source.zip` | d141a3ded8c2d9fe520c0c92ef82601f4e1b7ca3a5eb1580d018e33a8f4fd258 | S2 frozen Lean source |
| `outputs/oq7-paper1-publication/reproducibility/OQ7-complete-physical-theorem11.bundle` | 5a4e3a4623a910ee1f5993bc43b10da38d70125ef4aa74a22653b540b2db8479 | S2 frozen Git history |
| `outputs/oq7-paper1-publication/reproducibility/manifest.json` | 08aa0bd878602a9d112cf7d98d9bd7d22f9ae31c014f88a14396a292f18ec6a5 | S3 frozen verification manifest |
| `outputs/oq7-paper1-publication/reproducibility/AUDIT_PROVENANCE.md` | d6e8c40466eb90733bb48cc4a24bdf6da2304ad05d042f4d46aca9ab7959f26a | S4 audit provenance |
| `outputs/oq7-prescribed-extinction/PrescribedExtinction/PhysicalTheorem11.lean` | 656353efe23d729d63e17110540f52997dd4bacbeb607610b9853e3cad9ca180 | Claimed final theorem source |
| `outputs/oq7-prescribed-extinction/verification/claude-independent-audit-5a8350d.md` | 50d854e335d44cdf1d5a3710f3bc542a4a1a6c28593a46cd320a2ea6ed9f7245 | Independent baseline audit; examined 5a8350d5408c38e333c9f6b6d8a94816c794120b |
| `outputs/oq7/sources/original-checkpoint.md` | e142284fb1d2800f6a7e2c5346200b924435dded5e6b7793f5b2a4d7c1ee64f1 | Old uncompiled scalar-thickness checkpoint |
| `outputs/OQ7_Lean_verified.zip` | 0cf6849573f2d24992ae5d12359beb4bce4dc2a9bb4d3309d13904fce91cfe5b | Older Lean archive; scope to be confirmed by contents |
| `outputs/OQ7_Mission_Audit_2026-10-10.zip` | e4a4ec254a06012d94abf059e9ce5a6925dd2c78b1b55e69e3d53c61a34c6b5b | Older mission/audit archive; separate version |

## Skipped links

- `C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\oq7\.lake\packages` -> `C:\Users\Daniel\Documents\Codex\2026-10-09\set-up-a-local-ai-mathematical\outputs\math-research-lab\lean\.lake\packages`. Not traversed.
- `C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\oq7-mission\lean\.lake\packages` -> `C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\oq7\.lake\packages`. Not traversed.

## Initial missing items

- No substantive final-commit independent review has been identified so far. The located baseline audit examined 5a8350d5408c38e333c9f6b6d8a94816c794120b; the frozen manifest states final semantic review pending.
- Toolchain/dependency reproduction and fresh kernel replay are pending at this inventory stage.
- No independently implemented checker has yet been recovered or executed.

## Commit identity check

All 952 tracked commit files were SHA-256 compared with the original tree and frozen ZIP; 0 disagreements. See COMMIT_FILE_IDENTITIES.json and VERSION_AND_AUDIT_MAP.md. The distinct 43-authored-theorem finite-port supplement is **not recovered**; the older ZIP inventoried above contains the completed scalar project.
