import hashlib,json,pathlib,subprocess
root=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1'); work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\r59a36c60'); out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-release-20261013-final-audit-59a36c60');git=r'C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd\git.exe'
repo=work/'lean'; original='686402a6c2d63820828729cc7ab02504632e3fe7'
release=subprocess.check_output([git,'-C',str(repo),'rev-parse','HEAD']).decode().strip()
diff=subprocess.check_output([git,'-C',str(repo),'diff','--binary',original,'HEAD']).decode('utf-8')
(out/'PACKAGING_CHANGES.diff').write_text(diff,encoding='utf-8')
files=subprocess.check_output([git,'-C',str(repo),'diff','--name-status',original,'HEAD']).decode()
libs=[*sorted((repo/'OQ7').rglob('*.lean')),*sorted((repo/'PrescribedExtinction').rglob('*.lean')),repo/'OQ7.lean',repo/'PrescribedExtinction.lean']
mismatches=[]
for p in libs:
 rel=p.relative_to(repo).as_posix()
 frozen=root/'outputs/oq7-prescribed-extinction'/rel
 if hashlib.sha256(p.read_bytes()).digest()!=hashlib.sha256(frozen.read_bytes()).digest():mismatches.append(rel)
if mismatches:raise RuntimeError('Mathematical source changed')
inventory=json.loads(pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\OQ7-audit-20261013-a89f0ec7-128b-4db6-ae6a-40d4bf427076/source_inventory.json').read_text(encoding='utf-8-sig'))
changed=[]
for item in inventory:
 p=pathlib.Path(item['Path'])
 if not p.is_file():changed.append(item['Path']+' [missing]');continue
 sha=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):sha.update(block)
 if sha.hexdigest()!=item['SHA256']:changed.append(item['Path'])
for path,expected in [(pathlib.Path(r'C:/Users/Daniel/Downloads/AUDIT_REPORT_686402a.md'),'59a36c60a01d213c989ddf7547fbc63584770101b6eb5a6818bb3ad0d5f91eed'),(pathlib.Path(r'C:/Users/Daniel/Downloads/oq7-final-audit-686402a.zip'),'1e0c28039e81bcd9b5531a1e0d0e122190ef9780e9fec8d164467b5b1b032d30')]:
 if hashlib.sha256(path.read_bytes()).hexdigest()!=expected:changed.append(str(path))
preservation={'authorized_root':str(root),'original_regular_files_rehashed':len(inventory),'explicit_audit_attachments_rehashed':2,'original_changed_or_missing':changed,'mathematical_library_files':len(libs),'mathematical_source_mismatches':mismatches,'frozen_commit':original,'portable_release_commit':release,'note':'The original source census excludes the two untraversed dependency junctions. New work/output directories are separate.'}
(out/'ORIGINALS_PRESERVED.json').write_text(json.dumps(preservation,indent=2),encoding='utf-8')
if changed:raise RuntimeError('Original file changed')
(out/'RELEASE_DIFFERENCES.md').write_text(f"""# Separate release revision

Frozen audited commit: `{original}`.
Portable release commit: `{release}`.
The original commit, source ZIP, Git bundle, theorem and historical manuscripts remain unchanged. The release commits are confined to a disposable repository.

## Final changes

- R1: lake-manifest.json is included and tracked; its git-ignore rule was removed. sources/pinned-lake-manifest.json remains the tracked recovery copy.
- R2: lakefile.toml now uses the relative .lake/packages directory. Existing configure.py/configure.ps1 restore that default without changing a revision.
- Environment placeholders: portable top-level env.sh/env.ps1 use lake env; no manually assembled LEAN_PATH or machine-specific package path is required. The exact original auditor env.sh remains historical evidence.
- Added byte-preserved final audit programs/logs/report, preceding report, run-audit.py and a safe offline restore helper.
- Exported all nine dependency source ZIPs and Git metadata snapshots. Empty metadata directories are retained. Symbolic-link blobs are materialized as ordinary link-text files, matching core.symlinks=false, so restoration creates/follows no links.
- New manuscript edits change completed-audit status and review distinctions only. MANUSCRIPT_CHANGES.diff records them. Scientific theorem and equation environments remain unchanged.

All {len(libs)} mathematical library files have the same SHA-256 as the frozen originals. Added auditor theorems live under audit/final/experiments/; they do not replace or modify theorem11_complete. No dependency upgrade was made.

## Exact repository differences

```text
{files.strip()}
```

PACKAGING_CHANGES.diff supplies the full patch. Manuscript changes are outside this Git revision and have separate checksums and a full diff.

## Tests and scope

Current commands/logs are in portable-test-logs/ and results in PORTABLE_TEST_STATUS.json. The included compiler/dependency version checks and offline dependency round-trip are separate from the completed final semantic audit. This run tests on Windows; POSIX execution was not performed here.

The first offline restoration test rejected three dependency link entries; the helper was corrected to preserve their Git blob bytes as link-text without creating links. The next test found omitted empty Git metadata directories; export was corrected. Both failed attempts and the successful retest are retained. These were packaging tests, not failures of the audited theorem.
""",encoding='utf-8')
(out/'RELEASE_INDEX.md').write_text((out/'RELEASE_INDEX.md').read_text()+f'\nPortable release commit: `{release}`. Original audited commit: `{original}`. All 378 mathematical library source hashes are unchanged.\n',encoding='utf-8')
p=out/'REPRODUCE.md'; s=p.read_text();s=s.replace('restored Git HEAD to equal its pinned revision.','restored Git HEAD to equal its pinned revision. Dependency symbolic-link blobs are restored as link-text files under core.symlinks=false; no links are created or followed.');p.write_text(s,encoding='utf-8')
print(json.dumps(preservation,indent=2))
