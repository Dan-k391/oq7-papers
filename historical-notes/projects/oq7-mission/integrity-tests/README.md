# Isolated proof-integrity controls

These deliberately invalid fixtures are test inputs, not part of the OQ7 proof project. They live only in namespace `OQ7IntegrityScratch`, are compiled one file at a time, and never produce output `.olean` files. The original `outputs/oq7` source and configuration hashes are checked before and after the tests. No Lake build, dependency download, or source modification is performed.

The harness pins Lean 4.34.1, release commit `5045d0056413266e57c625dcd7c365b10e377c52`. It reads existing compiled OQ7 and Mathlib/dependency libraries through `LEAN_PATH`. The original Mathlib pin is `d13f23b723b8a846827a245b89c10fc7d3f11612`; dependency provenance is recorded by `../audits/existing-inventory.json`. The manifest's `Cli` package has no built Lean library and is not needed by these imports; the harness does not build it.

From this directory, on the current PC:

```powershell
.\run-integrity-tests.ps1
```

For another installation, pass the location of an unchanged existing OQ7 project and the official pinned compiler executable:

```powershell
.\run-integrity-tests.ps1 -ProjectRoot C:\research\oq7 -LeanExecutable C:\lean-4.34.1\bin\lean.exe
```

The harness independently observes four rejection mechanisms: compiler failure; a supplemental conservative source gate matching the preserved project; actual kernel `.axiomInfo` declarations in the scratch namespace; and transitive axiom closure obtained from `Lean.collectAxioms`, the same infrastructure used by `#print axioms`. Each discovered theorem must have a completed dependency census. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. The source regex is a conservative supplemental check, not a Lean parser; the census and dependency checks do not rely on that regex.

Executed results on 10 October 2026:

| Input | Compiler exit | Audit outcome | Required evidence actually observed |
|---|---:|---|---|
| Valid application of `OQ7.theorem51` for arbitrary parameters | 0 | Accepted | Exactly the three allowed foundations; comment tokens cause no rejection |
| False arithmetic proved by `rfl` | 1 | Rejected | Compiler reports failed `rfl`; its elaboration recovery additionally exposes `sorryAx` |
| False arithmetic using `sorry` | 0 | Rejected | Source gate and transitive `sorryAx` |
| `False` using `admit` | 0 | Rejected | Source gate and transitive `sorryAx` |
| Added `False` axiom used through an intermediate theorem | 0 | Rejected | Declared axiom census and forbidden transitive named axiom |
| Added unused axiom beside a valid arithmetic theorem | 0 | Rejected | Actual declared axiom census, although the theorem's own axiom list is empty |

All six expected outcomes were observed; all 83 original source/configuration hashes remained unchanged. The process exits zero only if every expected acceptance/rejection and compiler outcome is observed. Expected fixture compiler failures therefore do not mean that the harness failed. See `results.json`, `logs/`, and the generated case files for the exact evidence.

These controls test the audit against the stated failure modes. They do not prove compiler soundness or certify a Maxwell theorem by themselves. Scratch declarations are excluded from the 692 original authored theorem count.
