# Physical Theorem 1.1 — complete and kernel verified

`OQ7Prescribed.theorem11 : OQ7Prescribed.Theorem11Statement` is a kernel theorem declaration in PrescribedExtinction/Theorem11.lean. The exact final physical target is proved. There are no remaining Theorem 1.1 obligations.

The final fresh clean verification passed on 2026-10-11 at 21:15:54 UTC: 3568 build jobs, all 5402 inventoried public/private/generated project constants transitively audited, and clean pinned dependency source revisions. verification/report.json records VERIFIED, theorem11Verified=true, the exact final proof declaration, and identical-source clean-build equality. verification/final-theorem.log independently verifies theorem declaration kind, exact target type, and transitive axioms [propext, Classical.choice, Quot.sound]. Both final and isotropic-stability selected milestone builds/audits passed. Their reproducible logs and statement exports are under verification/milestones/.

The last intermediate commit was c0c5c16dd2a9061807d2f11b013f174282d0d6e4. The final completion commit includes the strict physical absorption/asymmetry result, actual tensor admissibility, second exact-extinction bracket and tuning, final witness assembly, and all clean-build/axiom certificates. Resolve its identity with git rev-parse HEAD; do not hard-code a self-referential commit hash into tracked evidence.

Reproduce from this repository:

```powershell
./verify.ps1 -LeanBin 'C:/Users/Daniel/Documents/Codex/2026-10-09/set-up-a-local-ai-mathematical/outputs/math-research-lab/tools/lean-4.34.1-windows/bin' -Clean
./verify-milestones.ps1 -LeanBin 'C:/Users/Daniel/Documents/Codex/2026-10-09/set-up-a-local-ai-mathematical/outputs/math-research-lab/tools/lean-4.34.1-windows/bin' -Only physical-theorem11
```

Verification needs access to external pinned dependency Git metadata; use approved escalated execution for the verifier when required by the sandbox. Never change accepted Lean sources during an audit. sources/ remains read-only and unchanged. Ignored work/ scratch is not accepted proof evidence.

The only historical target edit strengthens testing to all compact C-infinity curl tests, with exact source/snapshot hash guards. The entire final proposition body and original physical meaning are preserved. Maxwell.lean retains its historical unproved comments; the authoritative final proof is Theorem11.lean and the certificate is verification/report.json plus verification/final-theorem.log. Arbitrary outgoing-state uniqueness and converse volume representation are additional results outside this existential target, and no such unproved hypothesis enters theorem11.
