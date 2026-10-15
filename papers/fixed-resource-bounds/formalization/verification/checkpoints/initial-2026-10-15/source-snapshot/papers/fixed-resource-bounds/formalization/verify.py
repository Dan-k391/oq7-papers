"""Run this paper’s scope-aware pinned Lean verifier."""
from pathlib import Path
import runpy, sys
root=Path(__file__).resolve().parent
sys.argv[1:1]=["--project",str(root)]
runpy.run_path(str(root.parents[2]/"scripts/verify-companion-lean.py"),run_name="__main__")
