# Audited prescribed-extinction proof project

This directory contains the byte-preserved mathematical modules and portable build/audit scripts from the previously uploaded source repository. Directory relocation does not change module names.

Audited commit: 686402a6c2d63820828729cc7ab02504632e3fe7.
Portable source revision: 0bdf00f9b75b43194436f9536b1bf09463fd5a5d.
Final declaration: OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement.

From this directory, with the pinned Lean 4.34.1 distribution on PATH:

    python configure.py
    python restore-dependencies.py --archives-directory ../review-package/release/dependency-sources
    lake build OQ7 PrescribedExtinction
    lake env lean verification/FinalCompleteTheorem.lean
    python run-audit.py

Do not run lake update. The independent projects retained under historical-notes/ have different statements and coverage. Their existence is not substituted for the final Maxwell theorem. Earlier milestone documents in this directory retain their historical dates and partial-stage claims.
