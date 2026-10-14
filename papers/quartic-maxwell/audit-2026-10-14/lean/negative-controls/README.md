Negative controls for the audit Lean setup, run on 14 October 2026 in the same pinned environment.

- `NegSorry.lean`: an admitted false theorem. Elaboration reports "declaration uses `sorry`" and `#print axioms` lists `sorryAx`, which `scripts/run-paper-audit.py` rejects.
- `NegWrong.lean`: a deliberately wrong remainder constant (22/2000 instead of 21/2000). `norm_num` leaves the goal unsolved, and `lake env lean` exits with status 1.

These files are deliberately invalid and are not listed in `audit.json`.
