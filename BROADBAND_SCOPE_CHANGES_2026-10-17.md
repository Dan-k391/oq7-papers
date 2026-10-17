# Broadband scope revision — 17 October 2026

This revision updates the two current editable manuscripts under `papers/prescribed-extinction/arxiv/` and `papers/fixed-resource-bounds/arxiv/`, their local PDF/source packages, and the generated website. It does not imply remote deployment, preprint upload, or journal submission. Preserved publication manuscripts and historical evidence retain their original scope.

- **Prescribed extinction:** Section 9 defines a chosen band, exact center-frequency extinction, a band extinction floor, and a band objective for the same two-layer body and complete passive causal material law. It distinguishes frequency-local continuity from a prescribed-band result and explains that matching a Lorentz law at one frequency does not automatically preserve the material caps throughout a band. It separates the open unrestricted fixed-band unit-supremum question from the sharper fixed-resource optimum with joint causal constraints.
- **Fixed-resource bounds:** The bandwidth discussion makes explicit that existing pointwise gaps already imply band ceilings. Additional causal coupling across frequencies and joint realizability are not solved by those bounds.

Both manuscripts are dated 17 October 2026. Two unnumbered displays are added to the prescribed-extinction discussion. Existing theorem/proof bodies, prior displays, numbered equations and bibliographies are preserved. These are scope and exposition revisions, outside the existing proof verification; no new proof audit is claimed.

Build evidence for each revised manuscript belongs in its new `arxiv/BROADBAND_SCOPE_VERIFICATION_2026-10-17.json`, with build logs/configuration under `arxiv/verification/scope-2026-10-17/`. Those records describe the actual checks and outcomes. The build uses offline Tectonic 0.17.0, pinned bundle `6ffe055852f8faf66c0acbe1a7fb27f87b869a90bad1204f3bf4d9683f597c7c`, and `SOURCE_DATE_EPOCH=1792238400`.

Earlier `BUILD_VERIFICATION.json`, prescribed-extinction `FINALIZATION_VERIFICATION.json`, `SHA256SUMS`, and existing change reports are preserved byte-for-byte as historical records for their exact releases. They must not be read as verification of this revision. Formalization sources, dependency pins and frozen audit packages are preserved.
## Deployment follow-up

On 17 October 2026, the authorized revision was committed and pushed to `main` as `22fed75636f16309ccd0fb471e8674d62d258dc5`. The verified `papers/website/public/` files were deployed to `gh-pages` as `d2568df53e2116d75890c5e15dc2755960b8eafc`.

GitHub's Pages workflow completed successfully, and all 24 served files plus the directory landing page matched the verified local release. The initial `BROADBAND_SCOPE_REVIEW_2026-10-17.json` remains the pre-deployment review record. See [the subsequent deployment record](papers/website/verification/deployment-2026-10-17.json) for exact commit identities, live-file hashes, and verification time. Unrelated work remained uncommitted and unchanged.
