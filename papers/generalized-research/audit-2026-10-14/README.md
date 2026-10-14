# Generalized-research paper: audit of 14 October 2026

**Audited version:** the original `manuscript/OQ7_generalized_research_2026-10-10.pdf`, SHA-256 `3f01036f…77bf`. The arXiv reconstruction in `../arxiv/` was not audited.

This audit is AI-assisted and is not human peer review. It follows [AUDIT_WORKFLOW.md](../../../AUDIT_WORKFLOW.md). To reproduce it, run (`--kernel` adds about 5 minutes):

    python scripts/run-paper-audit.py papers/generalized-research/audit-2026-10-14 --kernel

## Verdict

All main results survive the audit.
- **Theorem 5.1** (sharp exact-target thickness asymptotic) is **fully kernel verified**. The manuscript itself said it was not (G-1).
- **Theorem 7.1** (prescribed-overlap envelope), **Theorem 6.4** (two-layer vector construction) and the channel bounds are correct as ordinary proofs.

No fatal error or proof gap was found. The findings concern the verification record (G-1, G-2) and an extraction hazard for auditors (G-3); see [MATHEMATICAL_AUDIT.md](MATHEMATICAL_AUDIT.md).

## Status of each result

| Result | Status | Evidence |
|---|---|---|
| Thm 5.1 | FULLY KERNEL VERIFIED. The Lean statement matches the manuscript; the closed-form layer transfer ↔ ODE (17) bridge is ordinary | `OQ7.theorem51 : ∀ p, OQ7.Theorem51Statement p`; axioms [propext, Classical.choice, Quot.sound]; `leanchecker --fresh OQ7.SharpPhysicalConstruction` exit 0; sources byte-identical to tag `audited-686402a` (78 files); logs in [logs/](logs/) |
| Lemmas 4.1–4.4, Thm 4.5 | ORDINARY PROOF (re-derived); used for finite stacks inside the Lean proof of Thm 5.1 | Audit A; checks |
| Cor. 5.2 | ORDINARY PROOF ONLY | Audit A |
| Props. 2.1–2.2, Prop. 6.1, Thm 6.2, (49), Thm 6.3 | ORDINARY PROOF ONLY (stated as known or derived from known results) | Audit A; random searches |
| Thm 6.4, Cor. 6.5, §6.6 | ORDINARY PROOF ONLY; numerics reproduced | `checks/` |
| Thm 7.1 | PARTIALLY FORMALIZED: the §7.4 rational instance is kernel-checked; the general certificate identities are verified numerically | `OQ7Mission.RationalOverlap` replay (22 declarations, standard axioms) |
| Appendix B (Lean 4.19 supplement) | Source not recovered; not credited | G-2 |

Checks: `checks/channel_and_planar_checks.py` passes 34/34, standard library only.

## Priority

Not certified. Besides the leads in the historical NOVELTY_REVIEW, a bounded search on 14 October found Sounas & Alù's February 2026 PRB letter (G-5). It has not been compared.

## Recommended follow-up (not done here)

Correct the formal-verification scope paragraph of the arXiv revision (`../arxiv/main.tex`, l. 660) to cite `OQ7.theorem51` and its replay records. The audited original remains unchanged.
