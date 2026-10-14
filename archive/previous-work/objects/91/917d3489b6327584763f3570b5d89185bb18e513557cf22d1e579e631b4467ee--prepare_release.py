import csv,difflib,gzip,hashlib,html,json,pathlib,re,shutil,stat,subprocess,zipfile
root=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1'); work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\r59a36c60'); out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-release-20261013-final-audit-59a36c60'); repo=work/'lean'; git=r'C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd\git.exe'
def cp(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(src,dst)
def put(path,s): path.parent.mkdir(parents=True,exist_ok=True); path.write_text(s,encoding='utf-8')
frozen=out/'frozen'; evidence=out/'evidence'; manuscript=out/'manuscript'; deps=out/'dependency-sources'
for p in [frozen,evidence,manuscript,deps]: p.mkdir(exist_ok=True)
exports=root/'outputs/oq7-physical-theorem11-review-686402a6c2d6'
for name in ['OQ7-complete-physical-theorem11-source.zip','OQ7-complete-physical-theorem11.bundle','manifest.json','INDEPENDENT_REVIEW_PROMPT.md','bundle-verify.log']:
 cp(exports/name,frozen/name)
cp(pathlib.Path(r'C:/Users/Daniel/Downloads/AUDIT_REPORT_686402a.md'),evidence/'AUDIT_REPORT_686402a.md')
cp(pathlib.Path(r'C:/Users/Daniel/Downloads/oq7-final-audit-686402a.zip'),evidence/'oq7-final-audit-686402a.zip')
with zipfile.ZipFile(evidence/'oq7-final-audit-686402a.zip') as z:
 for e in z.infolist():
  if e.is_dir(): continue
  p=pathlib.PurePosixPath(e.filename)
  if p.is_absolute() or '..' in p.parts or stat.S_ISLNK(e.external_attr>>16): raise RuntimeError('Unsafe evidence archive member')
  data=z.read(e); rel=pathlib.Path(*p.parts[1:])
  dest=repo/'audit/final'/rel; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data)
  dest=evidence/'final'/rel; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data)
  if rel.suffix=='.gz':
   dest.with_suffix('').write_bytes(gzip.decompress(data))
cp(root/'outputs/oq7-prescribed-extinction/verification/claude-independent-audit-5a8350d.md',evidence/'preceding/AUDIT_REPORT_5a8350d.md')
cp(evidence/'preceding/AUDIT_REPORT_5a8350d.md',repo/'audit/preceding/AUDIT_REPORT_5a8350d.md')
cp(root/'outputs/oq7-prescribed-extinction/sources/OQ7_prescribed_extinction_2026-10-11.pdf',evidence/'manuscripts/OQ7_prescribed_extinction_2026-10-11.pdf')
pub=root/'outputs/oq7-paper1-publication'
for name in ['main.tex','paper.pdf','theorem-correspondence.csv','MATHEMATICAL_CONSISTENCY.md','PUBLICATION_ISSUES.md','reproducibility/AUDIT_PROVENANCE.md']:
 cp(pub/name,evidence/'publication-baseline'/name)
for name in ['main.tex','references.bib','template.html','build.py','theorem-correspondence.csv','theorem-correspondence.html','figures/two-layer-geometry.pdf','figures/two-layer-geometry.svg','review/make_geometry.py']:
 cp(pub/name,manuscript/name)
for name in ['OQ7-complete-physical-theorem11-source.zip','OQ7-complete-physical-theorem11.bundle','manifest.json']:
 cp(frozen/name,manuscript/'reproducibility'/name)
cp(evidence/'AUDIT_REPORT_686402a.md',manuscript/'reproducibility/AUDIT_REPORT_686402a.md')
# Only formal-status prose changes in the manuscript.
text=(pub/'main.tex').read_text(encoding='utf-8-sig')
old=next(p for p in text.split('\n\n') if 'The repository certificates report a clean project build' in p)
new=r"""The final AI-assisted independent audit of commit \texttt{686402a6c2d63820828729cc7ab02504632e3fe7} reports PASS for Lean kernel validity, semantic fidelity to the original Theorem 1.1 and Lemma 1.2, Maxwell correctness within the formal model, both exact suprema and strict nonattainment, and closure of the preceding audit's F1--F4. These original statements correspond to Theorem~\ref{thm:main} and Lemma~\ref{lem:strict} here; the version comparison is supplied with the release. The final theorem uses only \texttt{propext}, \texttt{Classical.choice}, and \texttt{Quot.sound}. The auditor additionally proved \texttt{auditor\_extinction\_pos} and unconditional strictness for admissible bodies; those audit theorems are preserved separately, without changing the frozen main theorem. The \href{reproducibility/AUDIT_REPORT_686402a.md}{final audit report}, programs, and logs accompany this release."""
new+=r"""

The audit reports a fresh empty-environment replay of the \texttt{PhysicalTheorem11} import closure, using the same Lean kernel implementation. This is distinct from an independently implemented checker, which was not used. \href{reproducibility/manifest.json}{Supplement S3: frozen verification manifest} retains its historical export-time pending-review field; the completed final audit supersedes that status. \href{reproducibility/AUDIT_PROVENANCE.md}{Supplement S4: audit provenance} records both the preceding and final reviews. The audit establishes the main theorem's statement correspondence, not verification of every intermediate statement or this manuscript's reorganized proof presentation."""
text=text.replace(old,new)
old2=next(p for p in text.split('\n\n') if p.startswith('Kernel checking verifies the encoded implication.'))
text=text.replace(old2,r"""Kernel checking verifies the encoded implication. The completed AI-assisted semantic review assesses its correspondence with the stated Maxwell model; it is distinct from human peer review, which is not established by these materials. Scientific priority, experimental realization, and finite-resource or bandwidth performance remain separate questions. Neither formal verification nor absence of a retrieved equivalent publication establishes novelty.""")
put(manuscript/'main.tex',text)
put(out/'MANUSCRIPT_CHANGES.diff',''.join(difflib.unified_diff((pub/'main.tex').read_text(encoding='utf-8-sig').splitlines(True),text.splitlines(True),fromfile='preserved-publication/main.tex',tofile='release/manuscript/main.tex')))
# The mathematical theorem/equation environments must be byte-identical.
baseline=(pub/'main.tex').read_text(encoding='utf-8-sig')
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|equation)\}.*?\\end\{\1\}'
a=re.findall(pattern,baseline,re.S); b=re.findall(pattern,text,re.S)
blocks_a=[m.group() for m in re.finditer(pattern,baseline,re.S)]; blocks_b=[m.group() for m in re.finditer(pattern,text,re.S)]
if blocks_a!=blocks_b: raise RuntimeError('Mathematical block changed')
put(out/'MANUSCRIPT_PRESERVATION.json',json.dumps({'baseline_tex_sha256':hashlib.sha256((pub/'main.tex').read_bytes()).hexdigest(),'updated_tex_sha256':hashlib.sha256((manuscript/'main.tex').read_bytes()).hexdigest(),'mathematical_blocks_unchanged':True,'mathematical_blocks':len(blocks_a),'baseline_pdf_sha256':hashlib.sha256((pub/'paper.pdf').read_bytes()).hexdigest()},indent=2))
# Portable packaging fixes. Mathematical libraries remain unchanged.
ignore=(repo/'.gitignore').read_text(); put(repo/'.gitignore','\n'.join(x for x in ignore.splitlines() if x!='lake-manifest.json')+'\n')
put(repo/'env.sh',"""#!/bin/sh
# Source this file after activating the pinned Lean toolchain. Lake supplies LEAN_PATH.
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\\n' 'Activate Lean 4.34.1 before using this release.' >&2
  return 1 2>/dev/null || exit 1
fi
oq7_lean() { lake env lean "$@"; }
oq7_checker() { lake env leanchecker "$@"; }
""")
put(repo/'env.ps1',"""# Dot-source after activating Lean 4.34.1; Lake supplies the import path.
$ErrorActionPreference = 'Stop'
if (-not (Get-Command lake -ErrorAction SilentlyContinue)) { throw 'Activate Lean 4.34.1 first.' }
function Invoke-OQ7Lean { & lake env lean @args }
function Invoke-OQ7Checker { & lake env leanchecker @args }
""")
put(repo/'run-audit.py',"""\"\"\"Run the preserved final-audit programs through Lake's portable environment.\"\"\"
import pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
for name in ['Audit2.lean','AuditCone2.lean','AuditWholeProject.lean','AuditExperiments.lean']:
    result = subprocess.run(['lake','env','lean',str(root/'audit/final/experiments'/name)],cwd=root)
    if result.returncode: sys.exit(result.returncode)
""")
pins=json.loads((repo/'sources/pinned-lake-manifest.json').read_text(encoding='utf-8-sig'))
for p in pins['packages']:
 src=repo/'.lake/packages'/p['name']
 target=deps/(p['name']+'-'+p['rev']+'.zip')
 subprocess.run([git,'-C',str(src),'archive','--format=zip','--output='+str(target),p['rev']],check=True)
 if subprocess.check_output([git,'-C',str(src),'rev-parse','HEAD']).decode().strip()!=p['rev']: raise RuntimeError('Wrong dependency revision')
 if subprocess.check_output([git,'-C',str(src),'status','--porcelain','--untracked-files=no']).strip(): raise RuntimeError('Dirty dependency source')
put(deps/'PINNED_DEPENDENCIES.json',json.dumps(pins,indent=2)+'\n')
put(repo/'RELEASE_REPRODUCE.md',"""# Portable release revision
This revision preserves all 378 mathematical source files from commit 686402a6c2d63820828729cc7ab02504632e3fe7.
The root lake-manifest.json is tracked and available; sources/pinned-lake-manifest.json is retained.
The default package directory is .lake/packages. No absolute Windows path or manual LEAN_PATH is required.
Activate Lean 4.34.1, then run: python configure.py; lake build OQ7 PrescribedExtinction; python run-audit.py.
Dependency source ZIPs are supplied in the outer release's dependency-sources directory; restore them to .lake/packages by package name before building.
All package revisions are frozen. Do not run lake update or substitute other toolchain versions.
Original audit env.sh placeholders remain only in the historical audit packet; top-level env.sh and env.ps1 are portable convenience wrappers.
""")
print(json.dumps({'release':str(out),'portable_repository':str(repo),'dependency_archives':len(pins['packages']),'unchanged_math_blocks':len(blocks_a)}))
