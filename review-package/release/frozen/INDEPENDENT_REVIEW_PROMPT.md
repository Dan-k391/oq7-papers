Independently audit this frozen OQ7 Lean 4 repository. Check out the exact
commit in the accompanying frozen-review manifest and reproduce the build.
The audited baseline is 5a8350d5408c38e333c9f6b6d8a94816c794120b; the new
complete declaration is OQ7Prescribed.theorem11_complete with type
OQ7Prescribed.PhysicalTheorem11Statement. The preserved theorem11 is the
existence core, not the complete target by itself.

Find any discrepancy between the kernel-verified complete statement and
the original physical Maxwell Theorem 1.1 on manuscript page 3. Inspect the
manuscript directly. Unfold all relevant definitions and trace the entire
dependency chain. Do not trust this repository's verification reports,
the prior Claude audit, or any previous AI assessment.

Check separately:

1. Universal passivity and Gamma <= 1 for all original admissible states.
2. Outgoing weak Maxwell uniqueness almost everywhere, its existence,
   and the converse volume representation for arbitrary original states.
3. The forward optical theorem and X=A+S, with S identified as the actual
   full-sphere Poynting flux limit of the radiating representative.
4. Universal strict nonattainment at positive extinction, without an
   assumed common-extinction identity or constructed-family restriction.
5. Both exact fixed-extinction IsLUB/sSup values, over the entire original
   admissible class, and the unchanged exact prescribed-extinction witness.

Pay particular attention to whether weak-field equality is correctly
stated almost everywhere; whether the canonical exterior representative
is proved to represent the weak solution; whether all sphere integrals
are genuine; whether reciprocity establishes common extinction; and
whether the two value sets cover every physical body at the prescribed
extinction. Check physical normalizations, all directions and both
polarizations, matrix caps, the contact term, Maxwell well-posedness,
uniform aperture localization, and exact tuning after strictly positive
loss. Search for hidden assumptions, custom axioms, sorry/admit, unsafe
proof mechanisms, weakened claims, and vacuous structures or test classes.

Preserve all Lean sources and pinned revisions. In a separate disposable
checkout, build paths may be configured with configure.py/configure.ps1;
report those configuration changes. Rebuild and independently run the
exact-declaration checks, transitive axiom audit, and
leanchecker --fresh --verbose PrescribedExtinction. Adapt script execution
for your platform without changing the mathematical statements or proofs.

Report PASS, FAIL, or UNRESOLVED separately for kernel validity, semantic
fidelity, and mathematical completeness, as well as for each of the five
obligations. Provide exact source locations and counterexamples for any
problem. Distinguish a source kernel check, an empty-environment replay,
and an independently implemented kernel; do not conflate them.
