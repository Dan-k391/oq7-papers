# Scientific editorial revision — 29 October 2026

This pass revises the five current `arxiv/main.tex` manuscripts and the local website. It improves physical motivation, section transitions, the purpose of equations, and distinctions between results and their scope. The [reference-based writing framework](EDITORIAL_WRITING_FRAMEWORK_2026-10-29.md) records which passages of the seven requested papers were studied; no distinctive prose was copied. The references are models of communication, not evidence for these manuscripts' scientific claims.

## Scope and checks

An independent comparison of the original and revised sources found identical ordered inline and display math, numbered theorem/lemma/proposition/corollary blocks, citations, labels, cross-references and section headings. This is a text-preservation check, not proof verification; assumptions or prose interpretations can require separate scientific review. The five PDFs were compiled from the exact revised sources with Tectonic, and each source archive contains its revised `main.tex` and a notice that historical audit files retain their original version bindings. The independently verified local website uses fresh TeX auxiliary files for section, equation and citation numbering. Its [format report](website/verification/editorial-2026-10-29.json) checks source identity and links; it does not verify physics or deploy the website.

Original working manuscript files and prior website artifacts were saved under `.local/editorial-20261029/`. Historical publication snapshots, review packages, research-candidate notes and old verification records retain their previous versions. No Lean replay or new human review was performed. Existing formalization correspondence reports refer to the source hashes recorded in those reports; the revised TeX has a different hash.

## Changes by manuscript

- **Prescribed extinction:** clarifies the physical question, exact-extinction goal, role of the uniform aperture limit and order of the loss-regularization and retuning arguments. The broadband extension remains a candidate, and its complete existence theorem remains unproved.
- **Quartic Maxwell:** clarifies the small-object setting, real-linear-polarization restriction, distinction between a fixed-pattern expansion and the uniform upper theorem, and scope of exponent sharpness.
- **Fixed-resource bounds:** separates the material response budget, radiation-spectrum estimates, exact current relaxation and physical realizability; explains why a finite numerical sum has a controlled analytical tail.
- **Compact Maxwell cross sections:** explains the transition from point dipoles to finite bodies, the finite-to-planar comparison, the order of aperture/window limits and the role of positive loss.
- **Generalized research:** clarifies the scalar thickness problem, exact matching, channel certificate, and tensor example; separates abstract channel statements from physical realizability.

The local website explains the meaning of extinction and asymmetry and states that the broadband existence claim has not been fully formally verified or independently reviewed.

## Open scientific questions retained

The boundary and strict-floor broadband existence statements still require completion and independent checking, including their physical device construction. Fixed-resource and all-isotropic optima remain unresolved. The quartic claim is for opposite real linear polarizations; the companion cubic example concerns a broader complex-polarization class. Current relaxations need not be simultaneously realizable by one local material, and abstract channel equality does not establish a compact same-material Maxwell realization. The finite-cell strictness discussion in the generalized paper remains compressed and lies outside parts of its stated formal coverage. Prior-literature priority claims have not been newly audited.

## Build observations

All five PDF compilations succeeded without unresolved references or citations. The compact-cross-sections PDF reports an overfull line of 3.06 pt; the generalized-research PDF reports three overfull lines, up to 11.43 pt. These layout warnings remain for a later typographic pass; they do not establish a mathematical error. Detailed local logs and source preservation checks are in `.local/editorial-20261029/`.

## Exact revised source hashes

- `prescribed-extinction/arxiv/main.tex`: `f7ee99a1947e98083c0a755b28133f1499cef09189bb5ca3a8c5881f60baf308`
- `quartic-maxwell/arxiv/main.tex`: `eb3fa21191aa78bb7c671217a6949f768ea2d6e9863e2d76bbfce5bf1a6ca186`
- `fixed-resource-bounds/arxiv/main.tex`: `e80058f7914a593afcafd06325f591ae9e0ebf2add03455ec333950f09862de7`
- `compact-maxwell-cross-sections/arxiv/main.tex`: `f85fdac4c35c8eb677ecceab85a4829d6539d147900268b7825f7aa5a1f94c31`
- `generalized-research/arxiv/main.tex`: `721e1bc2ac3ec52cd613d1dd2ef5ecc7f1688c937cc347476e9b5809fb17fc1e`
