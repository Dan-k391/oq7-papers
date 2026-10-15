# Four companion papers: formalization changes — 15 October 2026

This is a verified **partial formalization checkpoint**, not completion of all four papers. No paper has been updated or declared fully verified as a result of this revision. Work began from main at `c46c974` after a fast-forward pull.

## Changes made

- Added `papers/fixed-resource-bounds/formalization/` as a real Lean project with five source modules, an aggregate, audit entry point, pinned toolchain, Lake configuration, verifier, exact public type guards, original/current claim ledger and immutable replay checkpoint. Its 48 public exports were checked for exact types and standard axioms and replayed by Lean's fresh kernel.
- Proved the measurable-support dyadic operator bound including null support, unique outgoing weak Maxwell fields, aperture-independent inverse bound, complex-polarization extinction reciprocity and positivity. Proved actual complete-sphere physical efficiency/work/paired contrast bounds for the uniform budget |D|K²/δ. Added the two-branch absolute-difference/cost algebra, exact anisotropic sphere tensor/coefficient calculations and the conditional fixed-order Bessel-energy argument.
- Added `papers/compact-maxwell-cross-sections/formalization/` with eight source modules and the same project/audit/checkpoint roles. Its 81 audited exports include one explicitly imported correspondence theorem.
- Proved the continuous-far-field strictness/directivity result; the complete physical six-vector dipole upper bound; literal equality tensors at every permitted extinction, including endpoints; their full passivity/reciprocity matrices and a free-extinction supremum of one with nonattainment. Checked the active-block bare-loss and radiation-dressing algebra separately.
- Connected the actual Green operator, full sphere radiation, outgoing weak-field uniqueness and physical flux to the compact manuscript. Derived its unrestricted two-layer dielectric supremum explicitly from the stronger unchanged prescribed-extinction theorem. This corollary does not certify the separate general-stack localization argument.
- Inventoried all twelve original fixed-resource statements, all thirteen original compact statements, and the compact reading revision's two additional labelled statements. Kept original PDFs, extracted texts and current TeX/PDF versions separately hash-bound. Original compact intermediate lemmas remain tracked even where they became unnumbered in the reconstruction.
- Added `scripts/verify-companion-lean.py` and per-project wrappers. The verifier rejects missing modules, omitted statement IDs, proof escapes, changed public types, nonstandard axioms, changed inputs, changed sources during replay and reused checkpoint directories. It saves the exact imported local source graph, objects, type/axiom inventory, replay logs and a source snapshot with a checksum manifest. Fresh replay uses the same Lean kernel implementation.
- Added `scripts/check-companion-controls.py` with positive and deliberately failing checks of the actual sphere coefficient, physical reciprocity signs and dipole loss-defect constraint.
- Added `scripts/check-companion-packaging.py` so the snapshot and delegated-status protection tests can be rerun from the repository.
- Updated `scripts/sync-paper-packages.py` so working proof projects own only their two formalization status documents. Existing manuscript snapshots retain their previous exact publication scope. Fixture checks confirm idempotence, status preservation, tamper detection, overwrite refusal and rejection of an incorrect delegated project identity. Production publication packages were not synchronized or rewritten.
- Revalidated the existing quartic and generalized proof/manuscript bindings. Their Lean sources, checked reports, guards and pinned dependencies are unchanged. Their earlier eight and fifteen numbered-statement results retain their separately recorded auxiliary limitations.
- Added this change record, a complete file-by-file JSON inventory, exact verification/preservation evidence and refreshed the collection checksum manifest.

## Work that remains

The fixed-resource ledger has 2 complete statements, 5 partial statements and 5 open statements. Major gaps are the general integrable response budget, complete ball radiation spectrum, exact resolvent floor and optimizer, sharp resource geometry, angular-cap estimate, dynamic anisotropic-sphere remainder and the local six-component extension. The verified uniform K²/δ budget does not replace the sharper manuscript budget.

The compact ledger has 6 complete entries (including two reading-revision additions), 1 partial entry and 8 open entries. Major gaps are the general Weyl fibers and grazing estimates, arbitrary-stack planar identities, smooth-window commutator, boundary-strip derivative estimates, general finite-aperture localization, square-aperture rate and the exact auxiliary planar/regularization lemmas. Original Proposition 3.3 remains partial pending its literal loss-operator factorization and full displayed identity package.

Unnumbered analytical statements, dispersion, numerical assertions, bibliography, novelty and human peer review are not certified by these kernel checks. The exact per-statement exports and remaining clauses are in each `formalization/verification/coverage.json` and `CLAIM_STATUS.md`.

## Preservation and records

All 2,225 protected existing files matched their pre-work hashes. Manuscripts, PDFs, bibliographies, arXiv upload ZIPs, published manuscript snapshots, prescribed-extinction sources, existing quartic/generalized proofs and original audits were preserved byte-for-byte. Daniel Wang remains first and Junjie Zheng second, with the existing consistent affiliation/email formatting. Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned.

- [Every added or modified file, with exact hashes](FOUR_PAPER_FORMALIZATION_CHANGE_INVENTORY.json)
- [Verification, preserved-file hashes and scope disposition](FOUR_PAPER_FORMALIZATION_VERIFICATION.json)
- [Fixed-resource claim ledger](papers/fixed-resource-bounds/formalization/verification/coverage.json)
- [Compact claim ledger](papers/compact-maxwell-cross-sections/formalization/verification/coverage.json)
- [Fixed-resource accepted checkpoint](papers/fixed-resource-bounds/formalization/verification/checkpoints/initial-2026-10-15/report.json)
- [Compact accepted checkpoint](papers/compact-maxwell-cross-sections/formalization/verification/checkpoints/initial-scoped-2026-10-15/report.json)

No preprint upload, journal submission or external contact was performed. Manuscript updates remain deferred until all required verification is complete.
