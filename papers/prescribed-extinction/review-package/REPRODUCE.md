# Reproduce this final review package

The exact audited theorem commit is 686402a6c2d63820828729cc7ab02504632e3fe7. The separately tested portable release commit is 0bdf00f9b75b43194436f9536b1bf09463fd5a5d. All 378 mathematical source modules are byte-identical. No dependencies were upgraded.

## Included tools, sources and pins

- toolchain/lean-4.34.1-windows.zip: exact recovered official Windows archive, SHA-256 457698d4e2132243e899ff32178d7ae63c16431d09ed9ad524d859c3581992af.
- Lean compiler: version 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52.
- release/dependency-sources/: nine complete pinned source snapshots and Git metadata archives, plus PINNED_DEPENDENCIES.json.
- Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612.
- release/frozen/ and supplements/S2_FROZEN_SOURCE.zip: exact audited source and complete Git bundle.
- release/portable-source.zip and release/portable-release.bundle: portable packaging revision.
- verification/: regenerated programs, commands, complete logs, versions and current status.
- release/portable-test-logs/ and release/evidence/final/logs/: prior completed clean/reproduction/auditor logs, preserved with their original provenance.

Python 3 and Git are needed. The manuscript also uses Tectonic 0.17.0 and Pandoc 3.12.1; their exact local paths are recorded in MANUSCRIPT_BUILD_COMMAND.json. Portable source paths are relative, and no absolute Windows package path is required.

## Portable proof reproduction

Verify SHA256SUMS from the package root. Extract the pinned Windows toolchain, put its bin directory on PATH, and confirm lean --version. Extract release/portable-source.zip to a new folder beside a copy of release/dependency-sources/. From that checkout run:

~~~text
python configure.py
python restore-dependencies.py --archives-directory ../dependency-sources
lake build OQ7 PrescribedExtinction
lake env lean verification/FinalCompleteTheorem.lean
python run-audit.py
lake env leanchecker --fresh --verbose PrescribedExtinction.PhysicalTheorem11
~~~

The restorer validates archive paths, restores exact Git revisions, refuses existing dependency directories and creates no dependency junctions or symbolic links. Do not run lake update. Use the included sources to rebuild dependency objects, or a compatible cache for the exact pins; describe which you used.

The finalization run copied a previously verified compatible dependency/project build cache into a **new isolated checkout**, checked exact dependency HEADs and clean tracked sources, and checked all mathematical source bytes against the frozen archive. Its regenerated Lake log is incremental/cached validation. The earlier 3,601-job clean build remains preserved evidence. This distinction is not hidden by calling both “clean builds.”

To regenerate the diagnostic outputs, copy verification/FinalType.lean, FinalAxioms.lean and CorrespondenceNames.lean into a release-diagnostics/ folder of the checkout, then run:

~~~text
lake env lean release-diagnostics/FinalType.lean
lake env lean release-diagnostics/FinalAxioms.lean
lake env lean release-diagnostics/CorrespondenceNames.lean
~~~

FinalType prints the elaborated type and defining statements/material/state structures with pp.all. FinalAxioms rejects any transitive dependency axiom beyond propext, Classical.choice and Quot.sound, and requires the exact theorem declaration/type. The preserved whole-project/cone auditor programs provide additional censuses. sorryAx, native-trust axioms or additional mathematical axioms are not acceptable for the strict claim.

leanchecker --fresh replays the target's full import environment into an empty kernel environment. This is Lean's **same kernel implementation**, not an independently implemented checker. Its source and command semantics were inspected in the pinned distribution. No independent-kernel checker is claimed.

## Manuscript reproduction

From manuscript/:

~~~text
python build.py --tectonic PATH_TO_TECTONIC --pandoc PATH_TO_PANDOC
~~~

These PATH arguments select executables, not hard-coded dependency package locations. The source, bibliography, vector assets and conversion helper are supplied. TeX-generated labels and bibliography numbering also drive the offline MathML HTML.

The frozen paper is preserved at frozen/paper.pdf. The review paper adds only documented attribution/status/disclosure changes. All mathematical environments and Sections 3–9 remain identical; see MANUSCRIPT_PRESERVATION.json and the editorial diff.

Windows reproduction is recorded here. POSIX execution and an independently implemented kernel checker are not claimed. No publication/upload/submission is part of reproduction.

