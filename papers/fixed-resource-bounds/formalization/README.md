# FixedResource: Lean formalization

This is an **incomplete paper-specific proof project**. The same `formalization/` layout, pinned Lean/Mathlib dependencies, namespace sources, aggregate, verifier, exact public type guards and immutable verification checkpoints are used as in the prescribed-extinction project.

Implemented proofs cover continuum Maxwell ingredients and additional results listed in [claim status](CLAIM_STATUS.md). A successful checkpoint certifies only its exact implemented declarations. The original PDF and reconstructed manuscript have separate recorded hashes. **The papers and arXiv upload files remain unchanged until all required verification is complete.**

Run from this directory after restoring the unchanged pinned dependencies and building the imported companion libraries:

```text
python verify.py --output-dir verification/checkpoints/NEW_RUN_NAME
```

The verifier compiles every local source, checks every exported type and axiom, and runs `leanchecker --fresh`. Use `--rebuild-dependencies` to recompile the entire imported local source graph. Build products stay in ignored `.lake/`; checkpoints are never overwritten. Fresh replay uses the same Lean kernel implementation, not an independent prover. Read [the scope ledger](verification/coverage.json) before citing verification.

The earlier publication package remains an exact snapshot of its earlier verification scope. It has not been promoted to a completely formalized manuscript.
