# Unit Supremum of Absorption Asymmetry at Prescribed Extinction for Compact Reciprocal Dielectrics

**Daniel Wang — McMaster University**

**Junjie Zheng — Columbia University**

This repository contains the manuscript, accompanying formal-verification evidence, and preserved earlier versions.

## Manuscript

- [Current PDF](publication/manuscript/paper.pdf), [HTML](publication/manuscript/paper.html), and [LaTeX source](publication/manuscript/main.tex)
- [Publication document index](publication/README.md), [author information](publication/AUTHOR_INFORMATION.md), and [revision record](publication/CHANGES.md)
- [S1–S4 supplements](publication/manuscript/reproducibility/SUPPLEMENT_INDEX.html)

The normalized asymmetry is the absolute absorption difference divided by the common dimensional extinction. For opposite unit-amplitude plane waves with the same real linear polarization, the theorem gives a unit supremum at every positive prescribed extinction within the stated compact two-layer reciprocal local nonmagnetic anisotropic dielectric class. Each individual body has strictly smaller asymmetry. Radiation accounting includes the full outgoing sphere and both transverse polarizations.

The theorem is at one frequency and under fixed pointwise upper material caps. Dimensions are unrestricted across the approximating sequence, with no common positive loss floor or bandwidth guarantee.

## Formal evidence

The audited declaration is `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement` at commit `686402a6c2d63820828729cc7ab02504632e3fe7`, preserved under tag `audited-686402a`. The portable packaging revision is tagged `portable-0bdf00f`. The publication revision does not change the mathematical source files.

- [Proof reproduction instructions](review-package/REPRODUCE.md) and [exact checking commands](review-package/verification/COMMANDS.jsonl)
- [Final audit report](review-package/release/evidence/AUDIT_REPORT_686402a.md), [claim-to-code correspondence](review-package/CLAIM_TO_CODE.md), and [audit provenance](publication/manuscript/reproducibility/AUDIT_PROVENANCE.md)
- [Pinned dependency identities](review-package/release/dependency-sources/PINNED_DEPENDENCIES.json)

The supplied checking records report only `propext`, `Classical.choice`, and `Quot.sound` as final-theorem dependency axioms. Fresh replay uses Lean's same kernel implementation. The mathematical and semantic reviews are AI-assisted; these materials do not establish completed human peer review, an independently implemented kernel check, or first scientific priority.

## Earlier versions

The [sealed October 13, 2026 review package](review-package/RELEASE_INDEX.md) retains the anonymous manuscript, original reports, logs, and checksums. Root-level milestone documents record successive earlier stages; their partial or pending statements are historical. The [version-specific disposition](review-package/VERSION_VERIFICATION_DISPOSITION.md) identifies the final evidence, and the [bounded priority comparison](review-package/priority/TARGETED_PRIORITY_REPORT.md) records unresolved literature comparisons.

The sealed checksum manifest includes a compiler archive omitted from ordinary Git files. The [upload provenance](GITHUB_UPLOAD.md) records the complete archive and compiler identities. Restoring that member is required to check every entry in the sealed manifest.
