"""Restore portable build paths while preserving every pinned dependency revision."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--packages-directory", type=Path,
                    help="Reuse an existing clean cache at the exact pinned revisions.")
args = parser.parse_args()
root = Path(__file__).resolve().parent
manifest = json.loads((root / "sources/pinned-lake-manifest.json").read_text(encoding="utf-8-sig"))
manifest["name"] = "oq7_prescribed_extinction"
packages = args.packages_directory.resolve().as_posix() if args.packages_directory else ".lake/packages"
if args.packages_directory and not args.packages_directory.is_dir():
    parser.error("The packages directory does not exist.")
manifest["packagesDir"] = packages
(root / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
(root / "lakefile.toml").write_text(f'''name = "oq7_prescribed_extinction"
version = "0.1.0"
packagesDir = {json.dumps(packages)}
defaultTargets = ["OQ7", "PrescribedExtinction"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"

[[lean_lib]]
name = "OQ7"

[[lean_lib]]
name = "PrescribedExtinction"
''', encoding="utf-8")
print(f"Configured pinned packages directory: {packages}")
