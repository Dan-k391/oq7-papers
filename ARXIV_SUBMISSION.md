# arXiv submission preparation

Use the current revisions under each paper's `arxiv/` directory. The October 10 PDFs are preserved originals; upload the new source packages instead.

| Manuscript | Current PDF | Source upload |
|---|---|---|
| Prescribed extinction for compact reciprocal dielectrics | [PDF](papers/prescribed-extinction/arxiv/paper.pdf) | [ZIP](papers/prescribed-extinction/arxiv/arxiv-source.zip) |
| Uniform quartic Maxwell asymmetry | [PDF](papers/quartic-maxwell/arxiv/paper.pdf) | [ZIP](papers/quartic-maxwell/arxiv/arxiv-source.zip) |
| Channel tradeoffs and scalar thickness asymptotics | [PDF](papers/generalized-research/arxiv/paper.pdf) | [ZIP](papers/generalized-research/arxiv/arxiv-source.zip) |
| Fixed-resource bounds | [PDF](papers/fixed-resource-bounds/arxiv/paper.pdf) | [ZIP](papers/fixed-resource-bounds/arxiv/arxiv-source.zip) |
| Compact Maxwell cross sections | [PDF](papers/compact-maxwell-cross-sections/arxiv/paper.pdf) | [ZIP](papers/compact-maxwell-cross-sections/arxiv/arxiv-source.zip) |

All five manuscript groups have editable revisions and their own source packages. This is a packaging distinction, not a claim that they provide five independent new contributions. In particular, the compact-Maxwell unrestricted supremum is implied by the stronger prescribed-extinction result. Its distinct dipole and fixed-aperture analysis should be positioned as companion material or consolidated with that paper before choosing separate submissions. The fixed-resource results also need to be positioned alongside the quartic refinement with their different illumination assumptions. The revision notes make these relationships explicit.

arXiv may ask authors to combine similar submissions or treat them as versions of one work, including when concepts and results overlap without extensive verbatim text. Decide the scientific separation before uploading all five packages as separate articles. [Version and similarity guidance](https://info.arxiv.org/help/versions.html)

## Authors and contacts

1. Daniel Wang, McMaster University, `denialk391@gmail.com`.
2. Junjie Zheng, Columbia University, `zjj2785@gmail.com`.

The personal addresses provide enduring correspondence if university account access ends. The affiliations describe the authors' current universities. Neither author is designated as corresponding author, and no department or ORCID is invented.

Associate the submitting author's school email with the arXiv account while it is accessible: `wangd170@mcmaster.ca` or `jz4168@columbia.edu`. arXiv encourages institutional email for first-time submitters to expedite endorsement. This is an account recommendation, not a claim that email domain determines scientific acceptance. [Endorsement guidance](https://info.arxiv.org/help/endorsement.html)

## Upload and review

The ZIPs contain compilation inputs only, with supporting evidence under `anc/` where supplied. They omit the compiled manuscript PDF, logs, auxiliaries, review notes and repository files. arXiv requires source for manuscripts produced from TeX and asks authors to remove extraneous files. Select PDFLaTeX and `main.tex`. [TeX guidance](https://info.arxiv.org/help/submit_tex.html), [accepted formats](https://info.arxiv.org/help/submit/index.html)

Before completing the submission, both authors should approve the final scientific text and authorship, choose the distribution license, and review arXiv's generated PDF and metadata. First submissions may require endorsement. Preparation here does not constitute an arXiv submission or moderation decision. [Submission guidance](https://info.arxiv.org/help/submit/index.html)

The local build checks use TeX Live 2024 with shell escape disabled, fresh compilation directories, resolved references and visual PDF inspection. The actual arXiv processing environment has not been tested. Results are recorded beside each manuscript in `BUILD_VERIFICATION.json`.

## Rebuild

From the repository root, with Python containing `pypdf` and TeX Live on PATH:

```text
python scripts/build-arxiv.py prescribed-extinction
python scripts/build-arxiv.py quartic-maxwell
python scripts/build-arxiv.py generalized-research
python scripts/build-arxiv.py fixed-resource-bounds
python scripts/build-arxiv.py compact-maxwell-cross-sections
```

On Windows, add `--tex-dir D:\texlive\2024\bin\windows` if needed. Outputs are `paper.pdf`, `arxiv-source.zip`, the processed bibliography where used, and `BUILD_VERIFICATION.json`. Build intermediates go into ignored `.local/arxiv-build/`. This workflow does not execute formal proof code.
