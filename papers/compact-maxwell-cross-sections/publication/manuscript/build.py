"""Rebuild canonical manuscript, then synchronize its publication snapshot."""
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parents[4]
subprocess.run([sys.executable,str(root/'scripts/build-arxiv.py'),'compact-maxwell-cross-sections',*sys.argv[1:]],check=True)
subprocess.run([sys.executable,str(root/'scripts/sync-paper-packages.py'),'--sync','--paper','compact-maxwell-cross-sections'],check=True)
