import hashlib,json,pathlib,subprocess,zipfile
root=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1'); work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\OQ7-audit-20261013-a89f0ec7-128b-4db6-ae6a-40d4bf427076'); out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-audit-20261013-a89f0ec7-128b-4db6-ae6a-40d4bf427076')
git=r'C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd\git.exe'; repo=work/'checkout'; commit='686402a6c2d63820828729cc7ab02504632e3fe7'
inventory=json.loads((work/'source_inventory.json').read_text(encoding='utf-8-sig'))
lookup={x['RelativePath'].replace('\\','/'):x for x in inventory}
def h(rel): return lookup[rel]['SHA256']
def read(rel): return (root/rel).read_text(encoding='utf-8-sig')
tree=subprocess.check_output([git,'-C',str(repo),'rev-parse',commit+'^{tree}']).decode().strip()
leaves=subprocess.check_output([git,'-C',str(repo),'ls-tree','-r','-z',commit]).split(b'\x00')
entries=[]
for leaf in leaves:
 if not leaf: continue
 info,name=leaf.split(b'\t',1); mode,typ,obj=info.split()
 entries.append((name.decode(),obj.decode(),mode.decode()))
proc=subprocess.Popen([git,'-C',str(repo),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
results=[]; disagreements=[]
archive=root/'outputs/oq7-physical-theorem11-review-686402a6c2d6/OQ7-complete-physical-theorem11-source.zip'
with zipfile.ZipFile(archive) as z:
 for name,obj,mode in entries:
  proc.stdin.write((obj+'\n').encode()); proc.stdin.flush()
  hdr=proc.stdout.readline().split(); size=int(hdr[2]); data=proc.stdout.read(size); proc.stdout.read(1)
  bh=hashlib.sha256(data).hexdigest()
  original=root/'outputs/oq7-prescribed-extinction'/name
  orig=h('outputs/oq7-prescribed-extinction/'+name) if 'outputs/oq7-prescribed-extinction/'+name in lookup else None
  archived=hashlib.sha256(z.read(name)).hexdigest() if name in z.namelist() else None
  results.append({'relative_path':name,'git_blob':obj,'mode':mode,'sha256':bh,'working_file_sha256':orig,'archive_member_sha256':archived,'working_matches_commit':bh==orig,'archive_matches_commit':bh==archived})
  if bh!=orig or bh!=archived: disagreements.append(name)
proc.stdin.close(); proc.wait()
(out/'COMMIT_FILE_IDENTITIES.json').write_text(json.dumps({'commit':commit,'tree':tree,'files':results,'disagreements':disagreements},indent=2),encoding='utf-8')
maptext=f"""# OQ7 version and audit map

Authorized root: `{root}`. Exact final commit recovered: `{commit}`, tree `{tree}`.
The frozen archive and original tracked working files were compared byte-for-byte by SHA-256 with every commit blob. Disagreements: {len(disagreements)}. Full identities are in COMMIT_FILE_IDENTITIES.json.

## Separate version families

| Family | Evidence and content identity | Actual scope / disposition |
|---|---|---|
| Old uncompiled scalar-thickness checkpoint | `outputs/oq7/sources/original-checkpoint.md`, SHA-256 `{h('outputs/oq7/sources/original-checkpoint.md')}` | Header explicitly says blocked before kernel verification, not a compiled Lean project. Target: scalar finite multilayer thickness asymptotic at fixed loss mass, transmitted power and mean absorptance. |
| Older 43-authored-theorem finite-port Lean supplement | Historical references describe a distinct Lean 4.19.0 supplement. No corresponding source/build package was recovered in the scanned root or archives. | **not recovered**. It is not the 692-theorem scalar project, 35-theorem mission components, or the final Maxwell repository. Historical reports are not source recovery. |
| Later completed scalar package | `outputs/oq7`; `outputs/OQ7_Lean_verified.zip`, SHA-256 `{h('outputs/OQ7_Lean_verified.zip')}`; saved inventory describes 77 modules, 692 authored theorems, 1288 kernel theorem constants | Separate one-dimensional scalar formalization, principal declaration `OQ7.theorem51`. Not substituted for the Maxwell theorem; not rebuilt by this audit. Counts are preserved evidence, not regenerated here. |
| Intermediate mission components | `outputs/oq7-mission/lean/verification/report.json` records 35 authored theorems; separate coercivity/work/rational SDP components | Explicitly partial physical coverage. Not the 43-theorem supplement or final Maxwell proof. |
| Claimed new full-Maxwell formalization | `outputs/oq7-prescribed-extinction` at `{commit}`; `PrescribedExtinction/PhysicalTheorem11.lean`, SHA-256 `{h('outputs/oq7-prescribed-extinction/PrescribedExtinction/PhysicalTheorem11.lean')}` | Exact requested source recovered. Principal declaration `OQ7Prescribed.theorem11_complete : PhysicalTheorem11Statement`. Fresh reproduction pending at this inventory stage. |

## Manuscript identities

| Version | SHA-256 | Pages / role |
|---|---|---|
| Primary `outputs/oq7-paper1-publication/paper.pdf` | `{h('outputs/oq7-paper1-publication/paper.pdf')}` | 16 pages; exact requested title; identical to `build/main.pdf` |
| Pre-minor preserved PDF | `{h('outputs/oq7-paper1-publication/review/pre-minor-2026-10-13/paper.pdf')}` | 16 pages; different content |
| Pre-correction preserved PDF | `{h('outputs/oq7-paper1-publication/review/pre-correction/paper.pdf')}` | 15 pages; different content |
| Frozen repository scientific specification | `{h('outputs/oq7-prescribed-extinction/sources/OQ7_prescribed_extinction_2026-10-11.pdf')}` | 19 pages; original Theorem 1.1 authority at baseline audit; not the current 16-page publication PDF |
| Old scalar note | `{h('outputs/oq7/sources/OQ7_verified_research_note.pdf')}` | 18 pages; distinct scalar-thickness theorem |

PDF_VERSION_INVENTORY.json includes all direct and archived PDF instances. Version labels above are backed by hashes and extracted contents, not timestamps alone.

## S1-S4 recovered

- S1: `outputs/oq7-paper1-publication/theorem-correspondence.csv` and `.html`.
- S2: `outputs/oq7-paper1-publication/reproducibility/OQ7-complete-physical-theorem11-source.zip` and `.bundle`. Hashes: `{h('outputs/oq7-paper1-publication/reproducibility/OQ7-complete-physical-theorem11-source.zip')}` and `{h('outputs/oq7-paper1-publication/reproducibility/OQ7-complete-physical-theorem11.bundle')}`. Each is byte-identical to its counterpart in `outputs/oq7-physical-theorem11-review-686402a6c2d6`.
- S3: `reproducibility/manifest.json`, SHA-256 `{h('outputs/oq7-paper1-publication/reproducibility/manifest.json')}`, and verification logs/reports inside S2. Their claims are historical until independently reproduced.
- S4: `reproducibility/AUDIT_PROVENANCE.md`, SHA-256 `{h('outputs/oq7-paper1-publication/reproducibility/AUDIT_PROVENANCE.md')}`. It identifies the older audit and unavailable named final report.

## Reviews and actual examined identities

| Review | Actual examined identity | Scope and limits |
|---|---|---|
| `verification/claude-independent-audit-5a8350d.md`, SHA-256 `{h('outputs/oq7-prescribed-extinction/verification/claude-independent-audit-5a8350d.md')}` | `5a8350d5408c38e333c9f6b6d8a94816c794120b`, tree `a1b03d72e958851f2418f97a6b5c40c0689e305c`; declaration `OQ7Prescribed.theorem11` | Kernel PASS, semantic fidelity FAIL, mathematical completeness FAIL for the existence-only baseline. Not a review of the final commit. |
| `oq7-paper1-publication/PUBLICATION_ISSUES.md` | Explicit source inspection of frozen `{commit}`; original manuscript `1e2e948a...` / PDF `1b925cad...`; later minor correction notes | AI-assisted publication/source correspondence review. Reports no confirmed P0 error and missing later independent review. It did not run a new complete replay. |
| `oq7-paper1-publication/MATHEMATICAL_CONSISTENCY.md`, SHA-256 `{h('outputs/oq7-paper1-publication/MATHEMATICAL_CONSISTENCY.md')}` | Final manuscript LaTeX `{h('outputs/oq7-paper1-publication/main.tex')}`, PDF `{h('outputs/oq7-paper1-publication/paper.pdf')}`; uses frozen final definitions | Focused mathematical checks of corrections; not a comprehensive independent final-commit semantic audit or human certification. |
| `oq7-mission/NOVELTY_REVIEW.md` | 41-page Paper A `3f01036f...` and 24-page Paper B `eb85dd06...` | Earlier priority/equivalence review of different manuscripts. It does not establish priority for the current prescribed-extinction theorem. |
| `OQ7_Final_Lean_Audit_686402a6.txt` or equivalent substantive final independent audit | No review body recovered | **not recovered**. The manifest and review prompt are not a completed review. |

The source and archive scans read 7760 text items and 27 PDF instances without reported extraction errors; nested archive identities are recorded. Searches stayed inside the corrected root and did not follow either dependency junction. No Downloads or other project location was searched in this audit. Historical S4 descriptions of wider searches are evidence about earlier work, not this audit's authorization.
"""
(out/'VERSION_AND_AUDIT_MAP.md').write_text(maptext,encoding='utf-8')
p=out/'INVENTORY.md'; s=p.read_text(); s+='\n## Commit identity check\n\nAll '+str(len(results))+' tracked commit files were SHA-256 compared with the original tree and frozen ZIP; '+str(len(disagreements))+' disagreements. See COMMIT_FILE_IDENTITIES.json and VERSION_AND_AUDIT_MAP.md. The distinct 43-authored-theorem finite-port supplement is **not recovered**; the older ZIP inventoried above contains the completed scalar project.\n'; p.write_text(s,encoding='utf-8')
print(json.dumps({'commit':commit,'tree':tree,'tracked_files':len(results),'disagreements':disagreements}))
