from pathlib import Path
import csv, hashlib, json, os
ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1")
OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-priority-20261013-7d4b21a9")
WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\p7d4b21a9")
BT=chr(96)
records=[]
for name in ["retrieval.json","retrieval_second.json","retrieval_final.json"]:
    records+=json.loads((WORK/name).read_text(encoding="utf-8"))
lookup={r["id"]:r for r in records}
sources=json.loads((WORK/"source_spec.json").read_text(encoding="utf-8"))
primary=[]
for id,title,label,version,url,locator,key in sources:
    r=dict(id=id,title=title,evidence=label,version=version,url=url,locator=locator)
    if key:
        raw=lookup[key]
        r.update(downloaded_pdf=key+".pdf",pdf_pages=raw.get("pages"),sha256=raw.get("sha256"),download_url=raw["url"])
    else:r.update(downloaded_pdf=None,sha256=None)
    primary.append(r)
inputs=[
("Frozen main theorem source","outputs/oq7-prescribed-extinction/PrescribedExtinction/PhysicalTheorem11.lean"),
("Audited October 11 manuscript, 19 pages","outputs/oq7-prescribed-extinction/sources/OQ7_prescribed_extinction_2026-10-11.pdf"),
("Release manuscript PDF, 16 pages","outputs/OQ7-release-20261013-final-audit-59a36c60/manuscript/paper.pdf"),
("Release manuscript source","outputs/OQ7-release-20261013-final-audit-59a36c60/manuscript/main.tex"),
("Own earlier compact variable-extinction manuscript","outputs/oq7-mission/references/OQ7_compact_Maxwell_cross_sections_2026-10-10.pdf"),
("Completed final audit report copy","outputs/OQ7-release-20261013-final-audit-59a36c60/manuscript/reproducibility/AUDIT_REPORT_686402a.md")]
input_records=[]
for purpose,rel in inputs:
    p=ROOT/rel
    if not p.is_file():raise RuntimeError("Missing input: "+str(p))
    for parent in [p,*p.parents]:
        if parent==ROOT.parent:break
        if os.lstat(parent).st_file_attributes & 0x400:raise RuntimeError("Reparse point input: "+str(parent))
    input_records.append(dict(purpose=purpose,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
registry=dict(date="2026-10-13",root=str(ROOT),root_literal_verified=True,repository_commit="686402a6c2d63820828729cc7ab02504632e3fe7",sources=primary,local_inputs=input_records,retrieval_attempts=records)
(OUT/"SOURCE_REGISTRY.json").write_text(json.dumps(registry,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
lines=["# Primary-source and version registry","","Date: 13 October 2026. Source IDs match COMPARISON_MATRIX.md. Exact downloaded bytes are identified by SHA-256, rather than filenames or dates alone. Null hashes mean no local full PDF was recovered. Downloaded literature stays in project scratch; the deliverables contain citations and short analysis, not copies of the papers.","","## Primary evidence inspected",""]
for r in primary:
    lines+=["### "+r["id"]+" — "+r["title"],"",f"- Evidence: **{r['evidence']}**. {r['version']}",f"- Primary link: [source]({r['url']}).",f"- Locator: {r['locator']}."]
    if r["sha256"]:lines+=[f"- Hashed local PDF: {BT}{r['downloaded_pdf']}{BT}; SHA-256 {BT}{r['sha256']}{BT}; {r['pdf_pages']} pages."]
    else:lines+=["- Full local PDF/hash: **not recovered**. Access does not support equation-level negative claims."]
    lines+=[""]
lines+=["## Local theorem/version anchors","","The corrected literal root exists: "+BT+str(ROOT)+BT+". These inputs and their ancestors were checked for reparse points; none were encountered. All local source inspection was beneath that root. The synced sources/ area and historical artifacts were not edited.","","Repository HEAD was read as "+BT+"686402a6c2d63820828729cc7ab02504632e3fe7"+BT+"; the frozen declaration is "+BT+"OQ7Prescribed.theorem11_complete"+BT+". The portable release revision is separate; no version of the older algebra packages was used as a substitute.",""]
for r in input_records:
    lines+=["- "+r["purpose"]+": "+BT+r["path"]+BT,"  SHA-256 "+BT+r["sha256"]+BT+"."]
lines+=["","## Access attempts and unresolved versions","","- Mann: official program, booklet, paper-submission information, exact-title/author conference and IEEE-scoped searches, and CUNY publications page inspected. No full contribution/identities recovered. The booklet is an abstract source, not a full proceedings paper.","- Gao: publisher introduction/previews, institutional publication listing, exact-title and NASA-scoped routes checked. Full pp.72–81 unrecovered. No author request or library request sent.","- Sounas 2014: primary abstract recovered; normal full-text/PDF links failed or returned non-PDF material. A guessed arXiv identifier was verified to be unrelated and excluded from the evidence.","- Yazdi: Aalto/KIT and author publication listings recovered; no article file was exposed. A coauthor dissertation located during the attempt is not treated as the Yazdi article.","- Máñez-Espina: publisher full prose retrieved by web. Publisher PDF returned 403; institutional bitstream displayed an anti-bot page. No challenge bypass or authenticated access was attempted. Supporting Information S1 remains unread.","- Bruno: full 2015 preprint inspected. Caltech lists the distinct final 28-page paper, and SIAM links wgf_method_supp_mats.zip. Normal final-PDF and supplement retrieval returned 403; the web's repository download link also yielded an inaccessible expired redirect. Final additions and detailed supplement derivations remain unverified.","- Khurgin: published author copy read through the web; local download encountered a certificate-chain verification error. The full preprint was recovered and separately hashed. It is not silently labeled the published PDF.","- Published-version equivalence of other author preprints/institutional reports was not assumed. Claims are tied to the explicitly inspected versions.","","Detailed public-URL retrieval results are preserved in SOURCE_REGISTRY.json. Full text was parsed for the relevant arguments; rendered equation pages were inspected where PDF text extraction was unreliable. This investigation does not audit the correctness of every prior-paper proof or claim completeness of the literature.","","## Output and preservation scope","","Only a uniquely named priority directory and scratch directory were created under the project. Existing proof, audit, release and manuscript files were preserved. This is a literature comparison; no Lean build, fresh replay or new general proof audit was commissioned in this run.",""]
(OUT/"SOURCE_REGISTRY.md").write_text("\n".join(lines),encoding="utf-8")
parts=(OUT/"COMPARISON_MATRIX.md").read_text(encoding="utf-8").splitlines()
tables=[];cur=[]
for line in parts:
    if line.startswith("|"):
        cur.append([v.strip() for v in line.strip("|").split("|")])
    elif cur:
        tables.append(cur);cur=[]
if cur:tables.append(cur)
merged={}
headers=["id","evidence"]
for ti,t in enumerate(tables):
    headers+=t[0][1:]
    for row in t[2:]:
        id=row[0].split(" / ")[0]
        if ti==0:merged[id]=[id,row[0].split(" / ")[1],*row[1:]]
        else:merged[id]+=row[1:]
with (OUT/"COMPARISON_MATRIX.csv").open("w",encoding="utf-8-sig",newline="") as f:
    wr=csv.writer(f);wr.writerow(headers);wr.writerows(merged.values())
print("source registry:",len(primary),"primary records;",len(input_records),"local inputs")
print("comparison CSV:",len(merged),"rows;",len(headers),"columns")

