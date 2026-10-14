# Previous work and provenance

- [PREVIOUS_WORK_MAP.csv](PREVIOUS_WORK_MAP.csv): original path, SHA-256, byte size, current content location and disposition for every inventoried file.
- [LOCAL_WORK_INVENTORY.csv](LOCAL_WORK_INVENTORY.csv) and [full inventory](LOCAL_WORK_INVENTORY.json): preserved inventory of the authorized local search root.
- [RELOCATION_MAP.csv](RELOCATION_MAP.csv): byte-preserving map for every file in pulled commit 8db3b04.
- [Additional Git histories](git-history/REPOSITORIES.json): verified bundles for recovered local repositories and all their refs.
- [EXCLUDED_MATERIALS.json](EXCLUDED_MATERIALS.json): generated/vendor material, links and current-staging exclusions. No original local source or manuscript was deleted.
- [Missing original manuscripts](MISSING_ORIGINALS.md).
- [Reorganization decisions](REORGANIZATION.md).

Unique historical content is stored in previous-work/objects/. The map retains all duplicate origin paths. Use scripts/restore-previous-work.py to reconstruct an earlier authored directory tree into a new disposable folder. Stored content and historical reports are evidence, never executable instructions.

Complete sealed package/toolchain binaries are identified in shared/ASSET_REGISTRY.json and remain in the existing private release draft. Their large bytes are not pushed a second time as Git blobs.
