import csv, hashlib, io, json, os, pathlib, re, stat, sys, zipfile
from pypdf import PdfReader
root=pathlib.Path(sys.argv[1]); work=pathlib.Path(sys.argv[2]); out=pathlib.Path(sys.argv[3])
files=json.loads((work/'source_inventory.json').read_text(encoding='utf-8-sig'))
byrel={f['RelativePath'].replace('\\','/'): f for f in files}
text_ext={'.md','.txt','.json','.csv','.tex','.html','.lean','.ps1','.py','.log','.toml','.bib'}
review_patterns=re.compile(r'686402a6|5a8350d|OQ7_Final_Lean_Audit|semantic fidelity|mathematical completeness|priority|43.authored|43 theorems', re.I)
records=[]; hits=[]; pdfs=[]; errors=[]; texts=0; archives=0
def checktext(label,data):
 global texts
 try: t=data.decode('utf-8-sig')
 except UnicodeDecodeError: return
 texts+=1
 if review_patterns.search(t):
  lines=[{'line':i,'text':l[:800]} for i,l in enumerate(t.splitlines(),1) if review_patterns.search(l)]
  hits.append({'path':label,'hits':lines[:150],'hit_count':len(lines)})
def archive(data,label,depth=0):
 global archives
 archives+=1
 try:
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   for e in z.infolist():
    if e.is_dir(): continue
    b=z.read(e)
    records.append({'Container':label,'Member':e.filename,'Bytes':len(b),'SHA256':hashlib.sha256(b).hexdigest(),'Symlink':stat.S_ISLNK(e.external_attr>>16)})
    suffix=pathlib.PurePosixPath(e.filename).suffix.lower()
    loc=label+'!/'+e.filename
    if suffix in text_ext: checktext(loc,b)
    if suffix=='.zip' and depth<4: archive(b,loc,depth+1)
    if suffix=='.pdf':
     p=PdfReader(io.BytesIO(b)); t='\n'.join(p.extract_text() or '' for p in p.pages)
     pdfs.append({'path':loc,'pages':len(p.pages),'sha256':hashlib.sha256(b).hexdigest(),'title_excerpt':t[:400]})
     checktext(loc,t.encode('utf-8'))
 except Exception as ex: errors.append({'path':label,'error':str(ex)})
for f in files:
 p=pathlib.Path(f['Path']); suffix=p.suffix.lower()
 if suffix in text_ext: checktext(f['RelativePath'],p.read_bytes())
 elif suffix=='.zip': archive(p.read_bytes(),f['RelativePath'])
 elif suffix=='.pdf':
  try:
   r=PdfReader(str(p)); t='\n'.join(page.extract_text() or '' for page in r.pages)
   pdfs.append({'path':f['RelativePath'],'pages':len(r.pages),'sha256':f['SHA256'],'title_excerpt':t[:400]})
   checktext(f['RelativePath'],t.encode('utf-8'))
   (work/('pdf_'+f['SHA256'][:12]+'.txt')).write_text(t,encoding='utf-8')
  except Exception as ex: errors.append({'path':f['RelativePath'],'error':str(ex)})
with (out/'ARCHIVE_MEMBER_HASHES.csv').open('w',newline='',encoding='utf-8') as stream:
 w=csv.DictWriter(stream,fieldnames=['Container','Member','Bytes','SHA256','Symlink']); w.writeheader(); w.writerows(records)
(work/'review_content_hits.json').write_text(json.dumps(hits,indent=2),encoding='utf-8')
(out/'PDF_VERSION_INVENTORY.json').write_text(json.dumps(pdfs,indent=2),encoding='utf-8')
summary={'direct_files':len(files),'text_items_scanned':texts,'archives_including_nested':archives,'archive_members':len(records),'pdf_instances':len(pdfs),'errors':errors}
(out/'SEARCH_COVERAGE.json').write_text(json.dumps(summary,indent=2),encoding='utf-8')
# Initial inventory, issued before reproduction.
main=['outputs/oq7-paper1-publication/paper.pdf','outputs/oq7-paper1-publication/main.tex','outputs/oq7-paper1-publication/theorem-correspondence.csv','outputs/oq7-paper1-publication/theorem-correspondence.html','outputs/oq7-paper1-publication/reproducibility/OQ7-complete-physical-theorem11-source.zip','outputs/oq7-paper1-publication/reproducibility/OQ7-complete-physical-theorem11.bundle','outputs/oq7-paper1-publication/reproducibility/manifest.json','outputs/oq7-paper1-publication/reproducibility/AUDIT_PROVENANCE.md','outputs/oq7-prescribed-extinction/PrescribedExtinction/PhysicalTheorem11.lean','outputs/oq7-prescribed-extinction/verification/claude-independent-audit-5a8350d.md','outputs/oq7/sources/original-checkpoint.md','outputs/OQ7_Lean_verified.zip','outputs/OQ7_Mission_Audit_2026-10-10.zip']
purposes=['Primary 16-page manuscript','Primary manuscript source','S1 theorem correspondence','S1 readable correspondence','S2 frozen Lean source','S2 frozen Git history','S3 frozen verification manifest','S4 audit provenance','Claimed final theorem source','Independent baseline audit; examined 5a8350d5408c38e333c9f6b6d8a94816c794120b','Old uncompiled scalar-thickness checkpoint','Older Lean archive; scope to be confirmed by contents','Older mission/audit archive; separate version']
lines=['# OQ7 inventory','', 'Initial inventory generated before reproduction. Recovery: exact final repository recovered.', '', 'Authorized root: `'+str(root)+'`.', '', 'Repository `outputs/oq7-prescribed-extinction` has observed HEAD `686402a6c2d63820828729cc7ab02504632e3fe7`. A detached disposable checkout was recovered from the frozen bundle. Original working tree preserved.', '', 'All '+str(len(files))+' direct regular files were SHA-256 hashed. SOURCE_FILE_HASHES.csv records exact absolute paths, sizes, hashes, and attributes, including hidden/ignored files. ARCHIVE_MEMBER_HASHES.csv inventories archive members, including nested ZIPs. PDF_VERSION_INVENTORY.json distinguishes PDFs by content hashes and page counts. No source junction was followed; both skipped junctions are listed below.', '', '| Artifact path relative to authorized root | SHA-256 | Purpose / commit attribution |', '|---|---|---|']
for key,purpose in zip(main,purposes):
 f=byrel.get(key)
 lines.append('| `'+key+'` | '+(f['SHA256'] if f else 'NOT RECOVERED')+' | '+purpose+' |')
links=json.loads((work/'skipped_links.json').read_text(encoding='utf-8-sig'))
lines+=['','## Skipped links','']+['- `'+x['Path']+'` -> `'+str(x['Target'])+'`. Not traversed.' for x in links]
lines+=['','## Initial missing items','', '- No substantive final-commit independent review has been identified so far. The located baseline audit examined 5a8350d5408c38e333c9f6b6d8a94816c794120b; the frozen manifest states final semantic review pending.', '- Toolchain/dependency reproduction and fresh kernel replay are pending at this inventory stage.', '- No independently implemented checker has yet been recovered or executed.']
(out/'INVENTORY.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
print(json.dumps(summary,indent=2))
print(json.dumps([p for p in pdfs if '!/' not in p['path']],indent=2))
