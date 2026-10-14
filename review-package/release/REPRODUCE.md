# Reproduce the portable release

The immutable original is in frozen/OQ7-complete-physical-theorem11.bundle and its byte-preserved source ZIP. The separate portable revision is in portable-source.zip and portable-release.bundle. The main mathematical source files and all dependency revisions are unchanged.

## Tools and exact pins

Use Lean 4.34.1, compiler commit 5045d0056413266e57c625dcd7c365b10e377c52. Lake reports 5.0.0-src+5045d00 for that release. Use Git and Python 3.

Official release: https://github.com/leanprover/lean4/releases/tag/v4.34.1
Windows ZIP SHA-256: 457698d4e2132243e899ff32178d7ae63c16431d09ed9ad524d859c3581992af
Linux tar.zst SHA-256: 47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4

Compiler binaries are not duplicated in this source release. Install/activate the exact official release. The nine exact library source archives and their Git metadata are included in dependency-sources/, with all revisions in PINNED_DEPENDENCIES.json.

## Portable checkout

1. Verify SHA256SUMS from the release root.
2. Extract portable-source.zip into a directory called portable beside dependency-sources/. Keep the checkout path reasonably short on Windows.
3. Activate the pinned Lean bin directory in PATH; verify lean --version.
4. From portable/, run:

```text
python configure.py
python restore-dependencies.py --archives-directory ../dependency-sources
lake build OQ7 PrescribedExtinction
lake env lean verification/FinalCompleteTheorem.lean
python run-audit.py
```

restore-dependencies.py refuses to overwrite existing dependency directories, validates archive paths and requires each restored Git HEAD to equal its pinned revision. Dependency symbolic-link blobs are restored as link-text files under core.symlinks=false; no links are created or followed. No dependency update is required. Alternatively, Lake may fetch the locked Git revisions online; do not run lake update.

The root lake-manifest.json is included and tracked. sources/pinned-lake-manifest.json remains a tracked recovery copy. Both use .lake/packages. configure.py and configure.ps1 restore the same relative configuration. Lake supplies the complete import environment; no manually assembled LEAN_PATH or absolute Windows dependency path is needed. The optional top-level env.sh/env.ps1 expose Lake wrappers after toolchain activation.

The original auditor's placeholder env.sh is preserved only under historical audit/final/ and evidence/final/. Do not source it; use the portable top-level wrapper or lake env.

Dependency compiled objects are not part of the archive. They can be rebuilt from included pinned sources; a compatible official Mathlib cache may accelerate this without changing pins. If using that cache, set MATHLIB_CACHE_DIR to a writable task-local directory before lake exe cache get.

## Existing audit programs

run-audit.py executes the byte-preserved Audit2.lean, AuditCone2.lean, AuditWholeProject.lean and AuditExperiments.lean through lake env. These include auditor_extinction_pos and related audit theorems. The final report and original logs are completed evidence even before a recipient reruns them.

Optional same-kernel fresh replay:

```text
lake env leanchecker --fresh --verbose PrescribedExtinction.PhysicalTheorem11
```

This repeats Lean's own kernel, not an independently implemented checker. The final auditor already reported a successful fresh replay. This release run does not claim a new independent kernel implementation.

## Manuscript

manuscript/main.tex and references.bib are the authoritative updated source; figure assets, build.py, template.html, PDF and offline MathML HTML are included. build.py uses Tectonic and Pandoc; provide their executable paths via --tectonic and --pandoc or put them in PATH. The current PDF was built with the previously available Tectonic 0.17.0 and Pandoc 3.12.1; the tools are not bundled.

The current Windows test built all 378 project modules in a fresh checkout, using compatible cached dependency objects at the locked revisions. It is not a new from-source build of all Mathlib. The final auditor reported its own from-source dependency build followed by fresh kernel replay; that completed evidence is preserved.

Complete current test commands, exit codes, versions, warnings and output are in portable-test-logs/. The original audit log archives remain in evidence/final/logs/. PORTABLE_TEST_STATUS.json records the current test outcome and limits. POSIX execution was not tested on this Windows host; the configuration uses relative paths and standard Lake/Python commands.

Nothing in these instructions expands the result to fixed resources, bandwidth, arbitrary compact geometries or every interpretation of OQ7.
