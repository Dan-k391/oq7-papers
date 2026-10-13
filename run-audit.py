"""Run the preserved final-audit programs through Lake's portable environment."""
import pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
for name in ['Audit2.lean','AuditCone2.lean','AuditWholeProject.lean','AuditExperiments.lean']:
    result = subprocess.run(['lake','env','lean',str(root/'audit/final/experiments'/name)],cwd=root)
    if result.returncode: sys.exit(result.returncode)
