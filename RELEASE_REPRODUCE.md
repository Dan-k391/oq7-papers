# Portable release revision
This revision preserves all 378 mathematical source files from commit 686402a6c2d63820828729cc7ab02504632e3fe7.
The root lake-manifest.json is tracked and available; sources/pinned-lake-manifest.json is retained.
The default package directory is .lake/packages. No absolute Windows path or manual LEAN_PATH is required.
Activate Lean 4.34.1, then run: python configure.py; lake build OQ7 PrescribedExtinction; python run-audit.py.
Dependency source ZIPs are supplied in the outer release's dependency-sources directory; restore them to .lake/packages by package name before building.
All package revisions are frozen. Do not run lake update or substitute other toolchain versions.
Original audit env.sh placeholders remain only in the historical audit packet; top-level env.sh and env.ps1 are portable convenience wrappers.
