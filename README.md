# OQ7 papers

Private collection of OQ7 manuscripts, proof sources, audits and reproducibility material. Current arXiv revisions are separate from the preserved historical manuscripts.

| Paper | Current material |
|---|---|
| [Prescribed extinction](papers/prescribed-extinction/arxiv/README.md) | Current editable arXiv revision; original publication and frozen verification records preserved |
| [Quartic Maxwell](papers/quartic-maxwell/README.md) | Revised manuscript; separate Lean theorem proofs, exact coverage and fresh kernel replay |
| [Fixed-resource bounds](papers/fixed-resource-bounds/README.md) | Reconstructed and revised TeX manuscript; original PDF and extracted text preserved |
| [Compact Maxwell cross sections](papers/compact-maxwell-cross-sections/README.md) | Reconstructed and revised companion manuscript; original PDF and extracted text preserved |
| [Generalized research](papers/generalized-research/README.md) | Revised manuscript; separate scalar, channel, overlap, thickness and planar-beam Lean proofs |

[Historical notes and earlier formalizations](historical-notes/README.md) remain separate from the final prescribed-extinction theorem. [Previous-work inventory](archive/README.md) maps every recovered origin by SHA-256; duplicate content is archived once. Build caches and downloaded tools are not research claims.

The current revisions list **Daniel Wang, McMaster University**, followed by **Junjie Zheng, Columbia University**. Their enduring contact addresses are **denialk391@gmail.com** and **zjj2785@gmail.com**, respectively. Earlier manuscripts and original audit bylines remain unchanged.

See [submission preparation](ARXIV_SUBMISSION.md), the preserved [reconstruction change record](ARXIV_CHANGES.md), the new [formalization changes](FORMALIZATION_CHANGES.md), and [PDF recovery status](archive/RECOVERY_STATUS_2026-10-14.md).

The preserved prescribed-extinction audit identifies commit 686402a6c2d63820828729cc7ab02504632e3fe7, tag audited-686402a; its portable packaging is tagged portable-0bdf00f. The new [quartic](papers/quartic-maxwell/formalization/README.md) and [generalized](papers/generalized-research/formalization/README.md) formalizations have separate version-bound records. See [all formalization changes](FORMALIZATION_CHANGES.md), the [file-by-file inventory](FORMALIZATION_CHANGE_INVENTORY.json) and the [current manuscript binding](FORMALIZATION_MANUSCRIPT_BINDING.json). Dependency pins and historical audit bytes remain unchanged. Formal verification does not establish novelty or human peer review.

Use [the configured primary workspace](WORKSPACE.md) when available. See [reproduction instructions](REPRODUCE.md) and the preserved [reorganization record](archive/REORGANIZATION.md). All collaborators with repository access can read and edit the collection.

Sibling-paper audits follow [AUDIT_WORKFLOW.md](AUDIT_WORKFLOW.md) and are re-run with `scripts/run-paper-audit.py`.
