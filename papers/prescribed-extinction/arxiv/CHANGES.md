# Prescribed-extinction finalization -- 15 October 2026

Baseline: clean `main` at `4012322cee9e3156dea70e1e923ff1bff3b4463b`; `git pull --ff-only origin main` reported already up to date. The current editable release is `arxiv/main.tex`, following the paper release index. The named publication manuscript at commit `8db3b0434e1cffcdd989359c747af428e71e6463` and all earlier review manuscripts remain historical versions.

## Editorial changes

- Added a short opening in Section 6 explaining selective absorption and polarization conversion in transmission. The auxiliary infinite planar zero-plate-loss model is distinguished from the finite compact objects with strictly positive tensor loss. The ideal reflectionless plate creates no backward reflection; stack reflection originates at the absorber, and scattering includes the change in transmission relative to vacuum.
- Explained after the plate-design equation that smaller permitted dielectric contrast requires a thicker plate. For each fixed cap P > 1 the integer j is chosen once and kept fixed throughout the construction.
- Dated the current manuscript 15 October 2026. Author order, affiliations, contact details and bibliography are unchanged.
- Regenerated the PDF, processed bibliography, arXiv source ZIP, build record and release checksums. The finalization verification record identifies the exact edited source and inspected pages.

The theorem, lemma, proposition, proof and displayed-equation bodies are unchanged. The same-material opposite-incidence requirement, exact positive prescribed extinction and both suprema, full-sphere two-polarization radiation, fixed upper material caps, unrestricted dimensions, lack of a common positive loss floor, and strict nonattainment are retained.

## Existing verification and outstanding review

The completed audit of frozen commit `686402a6c2d63820828729cc7ab02504632e3fe7` is existing evidence, not a newly performed audit. Its original report and status are preserved in `anc/`. It records PASS for kernel validity, semantic fidelity of the original main theorem and nonattainment lemma, Maxwell correctness within the formal model, both exact suprema, and closure of F1--F4. The current statement mapping is Theorem 4.1 and Lemma 4.2. The recorded empty-environment replay uses Lean's own kernel implementation; an independently implemented checker is not established. No proof build, new general audit or new kernel replay was commissioned for this editorial finalization.

The semantic evidence concerns the original main theorem and lemma, not every intermediate estimate in the differently organized exposition. It does not establish external human peer review or first priority. Equation-level comparisons with the unrecovered Mann--Alu conference work and complete Gao work, and priority for the rigorous uniform normalized finite-aperture construction at vanishing coupling, remain unresolved. Author and external human review remain separate from the completed formal verification. The theorem settles the stated resource-unrestricted, single-frequency prescribed-extinction formulation; it does not claim every interpretation of OQ7, a finite-resource optimizer, a bandwidth theorem or an all-isotropic realization.

The historical publication, sealed review package, frozen formalization and original audit records are preserved byte-for-byte. No publication, submission, upload or contact was performed. Local source-package compilation does not constitute testing on the arXiv server.

## Final build and release checks

The final 16-page PDF uses Tectonic 0.17.0, after restoring hash-verified compiler/cache copies into an isolated ignored build directory. Five missing font resources were fetched from the same bundle before the final offline build. The final PDF and a fresh offline rebuild from the 13-member source ZIP are byte-identical with the recorded fixed build timestamp. Both builds regenerate/resolve the bibliography and references; final logs have no citation/reference warnings or overfull/underfull boxes. All 20 bibliography entries are cited. All 51 displayed equations, five proof bodies and every theorem/lemma/proposition body match the preceding arXiv source.

All 16 pages were inspected as rendered images, including the Section 6 opening on pages 5--6, the fixed-j explanation and figure on page 7, verification scope on page 12, and complete references on pages 14--16. No clipping, overlaps, broken references or missing glyphs were observed. The final metadata-only reproducibility rebuild has identical page rasters. The new build has one more page than the prior PDF; no mathematical content was removed to preserve the old page count.

`FINALIZATION_VERIFICATION.json` records the checks, scope and inspected-page identities. `verification/PRESERVATION.json` records the baseline and unchanged protected groups. `verification/SOURCE_CHANGES.diff` records the exact source edit. `SHA256SUMS` covers this release directory except itself. The complete release ZIP additionally includes this PDF, source-upload ZIP, notes and verification records; it is a local delivery package, not an upload or submission.
