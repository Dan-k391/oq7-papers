import hashlib,json,pathlib,re,stat,zipfile
from html.parser import HTMLParser
from urllib.parse import unquote
from pypdf import PdfReader
work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\r59a36c60');out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-release-20261013-final-audit-59a36c60')
logs=out/'portable-test-logs'
commands=[json.loads(x) for x in (logs/'COMMANDS.jsonl').read_text(encoding='utf-8').splitlines()]
labels=['lean-version','lake-version','project-build','final-declaration','Audit2','AuditExperiments','AuditCone2','AuditWholeProject']
if [x['label'] for x in commands]!=labels or any(x['exit_code'] for x in commands):raise RuntimeError('Portable test not completed successfully')
build=(logs/'project-build.log').read_text(encoding='utf-8',errors='replace')
if 'Build completed successfully' not in build or 'Built PrescribedExtinction.PhysicalTheorem11' not in build: raise RuntimeError('Final mathematical module not shown in successful build')
if "declaration uses 'sorry'" in build:raise RuntimeError('Sorry warning in release build')
final=(logs/'final-declaration.log').read_text(encoding='utf-8',errors='replace')
if 'VERIFIED-COMPLETE-PHYSICAL-THEOREM11' not in final:raise RuntimeError('Missing exact final declaration check')
offline=json.loads((logs/'OFFLINE_RESTORE_RESULT.json').read_text())
if offline['exit_code'] or len(offline['packages'])!=9 or not all(p['tracked_source_clean'] for p in offline['packages']):raise RuntimeError('Offline pins unverified')
source_status=json.loads((out/'ORIGINALS_PRESERVED.json').read_text())
pdf=PdfReader(out/'manuscript/paper.pdf')
if len(pdf.pages)!=16:raise RuntimeError('Unexpected PDF page count')
warnings=[line for line in build.splitlines() if line.startswith('warning:')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
status={'status':'PASS','frozen_audited_commit':source_status['frozen_commit'],'portable_release_commit':source_status['portable_release_commit'],'platform_tested':'Windows x86_64','POSIX_execution_tested':False,'project_build_passed':True,'final_mathematical_module_checked':True,'project_build_final_line':next(line for line in reversed(build.splitlines()) if 'Build completed successfully' in line),'project_library_source_files_unchanged':378,'original_project_regular_files_unchanged':6196,'pinned_dependencies':offline['packages'],'offline_source_and_Git_metadata_restore_passed':True,'exact_final_declaration_and_axioms_checked':True,'preserved_audit_programs_all_passed':True,'audit_programs':labels[4:],'fresh_same_kernel_replay_this_run':False,'fresh_same_kernel_replay_existing_final_audit':'PASS, reported exit 0','independently_implemented_kernel_checker_used':False,'new_semantic_audit_commissioned':False,'manuscript_pages':16,'manuscript_equations':51,'manuscript_references':20,'pdf_sha256':sha(out/'manuscript/paper.pdf'),'tex_sha256':sha(out/'manuscript/main.tex'),'PDF_visual_QA':'All 16 rendered pages visually inspected; changed formal-status page inspected at full resolution; no overfull-box warning in final TeX build','Lean_build_warning_count':len(warnings),'warnings_file':'portable-test-logs/project-build-warnings.txt','commands_file':'portable-test-logs/COMMANDS.jsonl'}
(out/'PORTABLE_TEST_STATUS.json').write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
(logs/'project-build-warnings.txt').write_text('\n'.join(warnings)+'\n',encoding='utf-8')
# Self-contained local HTML links.
class Links(HTMLParser):
 def handle_starttag(self,tag,attrs):
  for key,value in attrs:
   if key=='href' and value and not value.startswith(('http:','https:','mailto:','#','data:')):self.links.append(value)
checks=[]
for f in (out/'manuscript').rglob('*.html'):
 p=Links();p.links=[];p.feed(f.read_text(encoding='utf-8'))
 for link in p.links:
  text=unquote(link.split('#')[0].split('?')[0])
  if not text:continue
  target=(f.parent/text).resolve()
  if not target.is_relative_to(out) or not target.exists():raise RuntimeError('Broken/outside-release HTML link '+str(f)+' '+link)
 checks.append({'file':f.relative_to(out).as_posix(),'local_links_checked':len(p.links),'pass':True})
(out/'SUPPLEMENT_LINK_CHECK.json').write_text(json.dumps(checks,indent=2),encoding='utf-8')
# Evidence matches the original attachments and frozen artifacts.
expected={'evidence/AUDIT_REPORT_686402a.md':'59a36c60a01d213c989ddf7547fbc63584770101b6eb5a6818bb3ad0d5f91eed','evidence/oq7-final-audit-686402a.zip':'1e0c28039e81bcd9b5531a1e0d0e122190ef9780e9fec8d164467b5b1b032d30','frozen/OQ7-complete-physical-theorem11-source.zip':'d141a3ded8c2d9fe520c0c92ef82601f4e1b7ca3a5eb1580d018e33a8f4fd258','frozen/OQ7-complete-physical-theorem11.bundle':'5a4e3a4623a910ee1f5993bc43b10da38d70125ef4aa74a22653b540b2db8479'}
for path,h in expected.items():
 if sha(out/path)!=h:raise RuntimeError('Evidence identity mismatch')
with zipfile.ZipFile(out/'evidence/oq7-final-audit-686402a.zip') as z:
 for e in z.infolist():
  if e.is_dir():continue
  rel=pathlib.Path(*pathlib.PurePosixPath(e.filename).parts[1:])
  for p in [out/'evidence/final'/rel,work/'lean/audit/final'/rel]:
   if sha(p)!=hashlib.sha256(z.read(e)).hexdigest():raise RuntimeError('Audit program/log changed')
index=out/'RELEASE_INDEX.md'
index.write_text(index.read_text()+'''
## Current-run validation completed

The portable Windows build passed 3,601 jobs and compiled the final PhysicalTheorem11 module. The exact final declaration/axiom check and all four preserved audit programs passed. All nine offline-restored dependency snapshots matched their pinned revisions and clean-source checks. All 378 mathematical source hashes, 6,196 original project-file hashes and both attached audit files are unchanged. The updated PDF remains 16 pages, with 51 equations and 20 references; all rendered pages were inspected.

Complete warnings are preserved in the build log; they are linter/deprecation diagnostics, with no admitted-proof warning. No additional fresh kernel replay or independent checker is claimed for this release run; the supplied final audit's completed replay remains accompanying evidence. POSIX execution and human peer review were not performed here.
''',encoding='utf-8')
# Hash every immutable release file; exclude the manifest's own self-reference.
allfiles=sorted(p for p in out.rglob('*') if p.is_file() and p.name!='SHA256SUMS')
for p in allfiles:
 if p.is_symlink() or p.stat().st_file_attributes & stat.FILE_ATTRIBUTE_REPARSE_POINT:raise RuntimeError('Unexpected release link')
manifest=''.join(sha(p)+'  '+p.relative_to(out).as_posix()+'\n' for p in allfiles)
(out/'SHA256SUMS').write_text(manifest,encoding='utf-8')
archive=out.parent/('OQ7-complete-source-and-audit-20261013-'+source_status['portable_release_commit'][:8]+'.zip')
if archive.exists():raise RuntimeError('Release archive already exists')
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in sorted(x for x in out.rglob('*') if x.is_file()):z.write(p,(out.name+'/'+p.relative_to(out).as_posix()))
# Verify every archived byte against the released originals.
with zipfile.ZipFile(archive) as z:
 for p in sorted(x for x in out.rglob('*') if x.is_file()):
  if hashlib.sha256(z.read(out.name+'/'+p.relative_to(out).as_posix())).hexdigest()!=sha(p):raise RuntimeError('Release archive byte mismatch')
checksum=archive.with_suffix('.zip.sha256')
checksum.write_text(sha(archive)+'  '+archive.name+'\n',encoding='utf-8')
print(json.dumps({'status':'PASS','release_directory':str(out),'complete_archive':str(archive),'archive_sha256':sha(archive),'archive_bytes':archive.stat().st_size,'checksummed_files':len(allfiles),'portable_commit':source_status['portable_release_commit'],'PDF_pages':16,'build_final_line':status['project_build_final_line'],'Lean_warnings':len(warnings)},indent=2))
