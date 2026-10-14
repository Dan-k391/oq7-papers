# Quartic Maxwell paper: audit of 14 October 2026

**Audited version:** the original `manuscript/OQ7_quartic_Maxwell_2026-10-10.pdf`, SHA-256 `576478ba…eac62`. The arXiv reconstruction in `../arxiv/` was not audited.

This audit is AI-assisted and is not human peer review. It follows [AUDIT_WORKFLOW.md](../../../AUDIT_WORKFLOW.md). To reproduce it, run:

    python scripts/run-paper-audit.py papers/quartic-maxwell/audit-2026-10-14

## Verdict

The three main theorems survive the audit.
- **Theorem 1.1** (uniform O((kR)⁴) bound over all measurable supports): correct once χ ∈ L^∞ is stated explicitly.
- **Theorem 1.2** (two-sphere coefficient interval and explicit remainder): correct.
- **Theorem 1.3** (sharp exponent in every resource class): correct.

No fatal error or proof gap was found. The only statement defect is the measurability hypothesis, Q-1 in [MATHEMATICAL_AUDIT.md](MATHEMATICAL_AUDIT.md). Two independent numerical routes corroborate the paper's unrecovered full-Maxwell table and its coefficient.

## Status of each result

| Result | Status | Evidence |
|---|---|---|
| Thm 1.1 | PARTIALLY FORMALIZED: ordinary proof independently re-derived; final algebraic chain kernel-checked with the operator estimates as hypotheses | `OQ7Quartic.quartic_chain` |
| Lemmas 3.1–3.4 | ORDINARY PROOF ONLY (re-derived) | MATHEMATICAL_AUDIT.md, Audit A |
| Thm 4.1 | ORDINARY PROOF ONLY (re-derived) | Audit A |
| Thm 1.2 | PARTIALLY FORMALIZED: every rational and surd constant of §5 kernel-checked and exact | `checks/certificates.py`, 61/61; `lean/QuarticCertificates.lean`, 18 declarations, standard axioms |
| Thm 1.3 | PARTIALLY FORMALIZED: constants of §6 kernel-checked; harmonic mean-value and interaction estimates re-derived | same |
| §7 numerics | Independently corroborated, not proof | `checks/two_sphere_crosscheck.py` |

The kernel checks ran on Lean 4.34.1 and Mathlib `d13f23b7`, using the pinned prescribed-extinction build environment. Negative controls behaved as expected: an admitted `sorry` was reported through `sorryAx`, and a deliberately wrong constant failed elaboration. No Maxwell operator is formalized. The prescribed-extinction kernel verification does not certify this paper.

## Priority

Not certified. A bounded search on 14 October found no uniform quartic theorem. The close precedents identified in the 10 October audit stand: Ammari–Deng–Millien imply fixed-shape quartic order, and Hopkins et al. give the two-dipole mechanism.

## Files

- [MATHEMATICAL_AUDIT.md](MATHEMATICAL_AUDIT.md): claim register, the three audit strands, classified issues and reconciliation with the earlier audit.
- [checks/](checks/): independent scripts using only the standard library, with their JSON results.
- [lean/QuarticCertificates.lean](lean/QuarticCertificates.lean) and its log in [logs/](logs/).
- [audit.json](audit.json): source hashes and steps for the runner.
