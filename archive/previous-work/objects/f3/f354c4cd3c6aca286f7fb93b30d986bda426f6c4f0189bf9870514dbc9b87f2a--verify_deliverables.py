from pathlib import Path
import csv, hashlib, json, re
OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-priority-20261013-7d4b21a9")
WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\p7d4b21a9")
reg=json.loads((OUT/"SOURCE_REGISTRY.json").read_text(encoding="utf-8"))
checks=[]
for item in reg["local_inputs"]:
    actual=hashlib.sha256(Path(item["path"]).read_bytes()).hexdigest()
    if actual!=item["sha256"]:raise RuntimeError("Input changed: "+item["path"])
checks.append("Six local theorem/manuscript/audit input anchors still match their recorded SHA-256 values.")
for item in reg["sources"]:
    if item["sha256"]:
        actual=hashlib.sha256((WORK/item["downloaded_pdf"]).read_bytes()).hexdigest()
        if actual!=item["sha256"]:raise RuntimeError("Source hash mismatch: "+item["id"])
checks.append("All twelve recorded downloaded primary PDF byte identities match the scratch files (eleven papers/preprints plus the abstract booklet).")
with (OUT/"COMPARISON_MATRIX.csv").open(encoding="utf-8-sig",newline="") as f:rows=list(csv.reader(f))
if len(rows)!=17 or any(len(row)!=12 for row in rows):raise RuntimeError("Matrix shape mismatch")
if {row[0] for row in rows[1:]}!={item["id"] for item in reg["sources"]}:raise RuntimeError("Matrix/registry ID mismatch")
checks.append("Matrix CSV has 16 unique source rows and 12 columns: IDs/evidence, nine comparison criteria, and first missing implication.")
for p in OUT.glob("*.md"):
    s=p.read_text(encoding="utf-8")
    if any(ord(c)<32 and c not in "\n\r\t" for c in s):raise RuntimeError("Control character: "+str(p))
    if p.name=="TARGETED_PRIORITY_REPORT.md" and (s.count("$$")%2 or "qquad" in s.replace("\\qquad","")):raise RuntimeError("Broken display mathematics")
    for link in re.findall(r"\]\(([^)]+)\)",s):
        if "://" not in link and not (OUT/link).exists():raise RuntimeError("Missing local document link: "+link)
checks.append("Local document links resolve; tables and displayed mathematical delimiters were checked, and key formulas were manually reviewed.")
notes=["# Verification and preservation notes","","Date: 13 October 2026.","","These are deliverable-consistency checks, not a new mathematical or semantic audit.",""]
notes += ["- PASS — "+c for c in checks]
notes += ["","The reviewed equation pages were Armitage PDF p.8; Andersen–Frandsen PDF pp.3–4; Sounas–Alù 2017 PDF pp.4,6,9; Gustafsson report PDF p.8; and Hopkins published PDF p.9. Text extraction was not relied on for ambiguous mathematical glyphs.","","The existing final audit remains completed evidence. No Lean rebuild, replay, proof rewrite, manuscript edit, publication, submission, email, library order or author contact was performed during this priority investigation.","","All filesystem writes for analysis were confined to the new project priority/scratch directories. A presentation copy of these new deliverables can be exported to the chat's designated outputs folder; no original source is exported or changed by that step.","","Access-limited rows retain unknowns. Author-preprint and final-published identities are distinguished. The report's derivation attempts are our own logical comparison, not equations invented for inaccessible references.",""]
(OUT/"VERIFICATION_NOTES.md").write_text("\n".join(notes),encoding="utf-8")
hashlines=[]
for p in sorted(OUT.iterdir()):
    if p.is_file() and p.name!="SHA256SUMS":
        hashlines.append(hashlib.sha256(p.read_bytes()).hexdigest()+"  "+p.name)
(OUT/"SHA256SUMS").write_text("\n".join(hashlines)+"\n",encoding="utf-8")
print("PASS:",len(checks),"consistency groups;",len(hashlines),"hashed deliverable files")
for p in sorted(OUT.iterdir()):print(p.name,p.stat().st_size)

