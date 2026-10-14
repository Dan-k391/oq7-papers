# Current version-specific verification disposition

This file describes current evidence. The preserved inventory-stage map is historical and is not a current verdict.

| Version family | Content identity | Supported claim |
|---|---|---|
| Old scalar-thickness checkpoint | historical/SCALAR_THICKNESS_CHECKPOINT.md; SHA-256 e142284fb1d2800f6a7e2c5346200b924435dded5e6b7793f5b2a4d7c1ee64f1 | Explicitly blocked before compilation/kernel verification. No successful verification claim is retained for that checkpoint. |
| Older 43-authored-theorem finite-port supplement | Source/build package **not recovered** in the authorized search; historical Lean 4.19.0 reports only | Source-specific kernel validity and full-Maxwell coverage cannot be independently substantiated. Historical counts do not supply the missing package. |
| Later scalar package OQ7.theorem51 | Separate OQ7_Lean_verified.zip; previous recorded SHA-256 0cf6849573f2d24992ae5d12359beb4bce4dc2a9bb4d3309d13904fce91cfe5b | Separate one-dimensional scalar formalization. Its historical verification is not evidence for the compact Maxwell theorem and is not freshly reproduced here. |
| Intermediate mission components | Separate 35-authored-theorem report | Partial components; neither the missing 43-theorem package nor the final Maxwell proof. |
| Earlier OQ7Prescribed existence-only stage | Commit 5a8350d5408c38e333c9f6b6d8a94816c794120b, preceding audit SHA-256 50d854e335d44cdf1d5a3710f3bc542a4a1a6c28593a46cd320a2ea6ed9f7245 | Earlier kernel PASS with semantic/completeness failures F1–F4. The review examined this earlier commit, not 686402a. |
| Final complete compact Maxwell theorem | Commit 686402a6c2d63820828729cc7ab02504632e3fe7; PhysicalTheorem11.lean SHA-256 656353efe23d729d63e17110540f52997dd4bacbeb607610b9853e3cad9ca180 | Exact source recovered. Completed final audit reports kernel PASS, main-statement semantic/model PASS and F1–F4 closed. Current regenerated checks are recorded separately. |
| Portable packaging revision | Commit 0bdf00f9b75b43194436f9536b1bf09463fd5a5d | Relative package configuration and tracked manifest; all 378 mathematical library source files match the frozen audited source. This is a release revision, not a new theorem. |
| This review manuscript | manuscript/main.tex and manuscript/paper.pdf; hashes in SHA256SUMS | Editorial correction/disclosures and existing priority-report linkage only; mathematical content unchanged from frozen/main.tex. This document revision is not attributed to the earlier auditor. |

The exact final Lean source is available and sufficient for the supported main-theorem verification claim; the ordinary-only fallback requested by the user is therefore not triggered. No formal claim is transferred from the scalar or finite-port versions.

The historical manifest's export-time “semantic review not yet performed” field is preserved and explicitly superseded by the recovered completed final report. The older inventory-stage statement that the final audit was not recovered is likewise historical; it does not describe the final package.

The frozen 16-page publication baseline (SHA-256 aa3a3fdb569a69d9fef82ecd54fe94d346f3723a0e65f597c24ac18ee3e1890d), the 19-page October 11 specification (SHA-256 3d9775d849234e828370d7c96d8bdcdd574beb6831a7906ea6b7706579868710), and the completed-audit release PDF (SHA-256 a9aca2e3ac18219338bfc8f6f237df24935c8693a4aad3986784ea462be44ec9) remain separate content versions. The last is also preserved as frozen/paper.pdf. New review fingerprints do not rename or retroactively redate those originals.

