"""Verify format inventories, source preservation, and final release integrity."""
from pathlib import Path
import csv
import base64
import hashlib
import json
import re
import subprocess
import xml.etree.ElementTree as ET
from lxml import html as lhtml
import pdfplumber
from pypdf import PdfReader

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent/"oq7-prescribed-extinction"
errors=[]
def require(condition,message):
    if not condition: errors.append(message)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

formats=json.loads((ROOT/"build/format-correspondence.json").read_text(encoding="utf-8"))
for name,sha in formats["source_sha256"].items():
    require(digest(ROOT/name)==sha,"Rendered source is stale: "+name)
log=(ROOT/"build/main.log").read_text(encoding="utf-8",errors="replace")
tex_issues=re.findall(r"(?:Overfull|Underfull)[^\n]*|LaTeX Warning:[^\n]*|! [^\n]*",log)
require(not tex_issues,"Final TeX log contains layout/citation errors")
doc=lhtml.fromstring((ROOT/"paper.html").read_bytes())
ids=doc.xpath('//*[@id]/@id')
require(len(ids)==len(set(ids)),"Duplicate HTML IDs")
hrefs=doc.xpath('//a[starts-with(@href,"#")]/@href')
missing=[href[1:] for href in hrefs if href[1:] not in ids]
require(not missing,"Unresolved HTML references")
equations=doc.xpath('//*[contains(concat(" ",normalize-space(@class)," ")," equation ")]')
require({e.get("id") for e in equations}==set(formats["equation_labels"]),"Equation labels differ")
require(len(doc.xpath('//math'))==formats["math_expressions"],"MathML expression inventory differs")
require(not doc.xpath('//merror'),"MathML errors")
require(len(doc.xpath('//ol[@class="references"]/li'))==formats["references"],"Reference count differs")
require(not doc.xpath('//script[@src] | //link[@rel="stylesheet"]'),"HTML has remote rendering dependencies")
images=doc.xpath('//figure//img')
require(len(images)==formats["figures"]==1,"Figure inventory differs")
require(all(e.get("src","").startswith("data:image/svg+xml;base64,") for e in images),"Figure not embedded as vector SVG")
require(base64.b64decode(images[0].get("src").split(",",1)[1])==(ROOT/"figures/two-layer-geometry.svg").read_bytes(),"Embedded figure differs from authoritative SVG")
for name,sha in formats["figure_sources"].items():
    require(digest(ROOT/name)==sha,"Figure source stale: "+name)
require(doc.xpath('//figure/@id')==formats["figure_labels"],"Figure label differs")
require(doc.xpath('//figure/figcaption')[0].text_content().startswith("Figure 1."),"Figure caption numbering differs")
require(doc.xpath('//figure//a[@href="figures/two-layer-geometry.svg"]'),"Full-size vector figure access missing")
aux=(ROOT/"build/main.aux").read_text(encoding="utf-8")
labels=dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}",aux))
for e in equations:
    require(e.get("data-number")==labels[e.get("id")],"Equation number mismatch: "+e.get("id"))
headnums=re.findall(r"\\contentsline \{(?:section|subsection)\}\{\\numberline \{([^}]+)\}",aux)
heads=doc.xpath('//main/h2 | //main/h3')
require(len(heads)==len(headnums),"Numbered section inventory differs")
for heading,n in zip(heads,headnums):
    require(heading.text_content().startswith(n+" "),"Heading number mismatch: "+heading.text_content())
reader=PdfReader(ROOT/"paper.pdf")
figure_labels=[e.text for e in ET.fromstring((ROOT/"figures/two-layer-geometry.svg").read_bytes()).iter("{http://www.w3.org/2000/svg}text")]
figure_pdf_text=PdfReader(ROOT/"figures/two-layer-geometry.pdf").pages[0].extract_text()
require(all(re.sub(r"\s+","",s) in re.sub(r"\s+","",figure_pdf_text) for s in figure_labels),"Vector PDF/SVG label mismatch")
pdf_destinations=[]
for page in reader.pages:
    for ref in page.get("/Annots",[]):
        annotation=ref.get_object()
        dest=annotation.get("/Dest")
        action=annotation.get("/A")
        if dest is None and action and action.get("/S")=="/GoTo":
            dest=action.get("/D")
        if isinstance(dest,str):
            pdf_destinations.append(dest)
require(all(d in reader.named_destinations for d in pdf_destinations),"PDF internal destination missing")
pdftexts=[p.extract_text() for p in reader.pages]
require(all(t.strip() for t in pdftexts),"Empty PDF page")
require(all("\ufffd" not in t for t in pdftexts),"Replacement glyph in PDF text")
require(len(reader.pages)==16,"Unexpected final page count (16 pages after focused corrections)")
pdftext="\n".join(pdftexts)
require("PrescribedExtinction/PhysicalTheorem11.lean" in pdftext,"Source path missing from PDF")
require("PrescribedExtinction/PhysicalTheorem11.lean" in doc.text_content(),"Source path missing from HTML")
for i in range(1,formats["equations"]+1):
    require("("+str(i)+")" in pdftext,f"PDF equation {i} missing")
for i in range(1,formats["references"]+1):
    require("["+str(i)+"]" in pdftext,f"PDF reference {i} missing")
bounds=[]
with pdfplumber.open(ROOT/"paper.pdf") as pdf:
    for i,page in enumerate(pdf.pages):
        words=page.extract_words()
        bad=[w for w in words if w["x0"]<65 or w["x1"]>547 or w["top"]<55 or w["bottom"]>760]
        if bad: bounds.append(dict(page=i+1,words=[w["text"] for w in bad]))
require(not bounds,"PDF text outside checked page margins")
browser=json.loads((ROOT/"review/html-render-check.json").read_text(encoding="utf-8"))
for r in browser:
    require(r["documentWidth"]<=r["viewport"]+1,"Browser page overflow")
    require(r["mathErrors"]==0 and not r["missingLinks"] and not r["duplicateIds"],"Browser semantic/render errors")
    require(r["equations"]==formats["equations"] and r["mathExpressions"]==formats["math_expressions"] and r["references"]==formats["references"],"Browser format inventory differs")
    require(r["figures"]==1 and r["imagesLoaded"],"Browser figure missing")
    require(r["overflowingEquationsAccessible"],"Long equation lacks scroll access indication")
    require(r.get("keyboardScrollWorks",True) and r.get("fullEquationReachable",True),"Mobile equation keyboard/full scroll check failed")
cert=json.loads((REPO/"verification/report.json").read_text(encoding="utf-8-sig"))
mismatches=[s["file"] for s in cert["sourceHashes"] if digest(REPO/s["file"]).lower()!=s["sha256"].lower()]
require(not mismatches,"Frozen source hashes changed")
status=subprocess.check_output(["git","status","--porcelain"],cwd=REPO,text=True)
commit=subprocess.check_output(["git","rev-parse","HEAD"],cwd=REPO,text=True).strip()
require(not status,"Frozen Git checkout modified")
require(commit=="686402a6c2d63820828729cc7ab02504632e3fe7","Frozen commit changed")
inputs=json.loads((ROOT/"review/input-manifest.json").read_text(encoding="utf-8"))
require(all(digest(Path(s["path"]))==s["sha256"] for s in inputs),"Original input changed")
copies=json.loads((ROOT/"reproducibility/copy-manifest.json").read_text(encoding="utf-8"))
require(all(digest(ROOT/"reproducibility"/s["name"])==s["sha256"] for s in copies),"Copied frozen artifact changed")
with (ROOT/"theorem-correspondence.csv").open(encoding="utf-8-sig",newline="") as f:
    rows=list(csv.DictReader(f))
require(len(rows)==53,"Correspondence row inventory changed")
for row in rows:
    require(row["manuscript_number"]==labels.get(row["manuscript_label"],""),"Stale correspondence numbering")
checks=(ROOT/"review/correspondence-lean-check.log").read_text(encoding="utf-8-sig")
require("error:" not in checks.lower(),"Correspondence Lean check failed")
for row in rows:
    for name in row["lean_declarations"].split("; ") if row["lean_declarations"] else []:
        require(name in checks,"Correspondence declaration missing from current log: "+name)
def math_nodes(o):
    if isinstance(o,dict):
        if o.get("t")=="Math": yield o["c"][1]
        for v in o.values(): yield from math_nodes(v)
    elif isinstance(o,list):
        for v in o: yield from math_nodes(v)
def normal_math(s):
    s=re.sub(r"\\label\{[^}]+\}","",s)
    s=s.replace(r"\begin{equation}","").replace(r"\end{equation}","")
    return re.sub(r"\s+","",s)
pandoc=next((ROOT/"tools/pandoc").rglob("pandoc.exe"))
raw=json.loads(subprocess.check_output([str(pandoc),"main.tex","-f","latex","-t","json"],cwd=ROOT,text=True,encoding="utf-8"))
source_math=[normal_math(s) for s in math_nodes(raw)]
html_math=[normal_math(e.text or "") for e in doc.xpath('//annotation[@encoding="application/x-tex"]')]
require(source_math==html_math,"HTML math content/order differs from fresh authoritative LaTeX parse")
original=(ROOT/"review/pre-correction/main.tex").read_text(encoding="utf-8")
current=(ROOT/"main.tex").read_text(encoding="utf-8")
def statement(src,label):
    return re.search(r"\\begin\{theorem\}[^\n]*\\label\{"+re.escape(label)+r"\}.*?\\end\{theorem\}",src,re.S).group(0)
require(statement(original,"thm:main")==statement(current,"thm:main"),"Theorem 4.1 changed")
require(statement(original,"thm:aperture")==statement(current,"thm:aperture"),"Theorem 7.1 changed")
old_eq=dict(re.findall(r"\\begin\{equation\}\\label\{([^}]+)\}(.*?)\\end\{equation\}",original,re.S))
new_eq=dict(re.findall(r"\\begin\{equation\}\\label\{([^}]+)\}(.*?)\\end\{equation\}",current,re.S))
changed_eq=[key for key in old_eq if old_eq[key]!=new_eq.get(key)]
require(changed_eq==["eq:commutator"],"Unexpected scientific equation change")
require(new_eq["eq:commutator"]==old_eq["eq:commutator"].replace(r"\widehat H",r"\widehat{\widetilde H}"),"Eq. (35) changed beyond intended global-field notation")
for href in doc.xpath('//a/@href'):
    if not href.startswith(("#","http:","https:","mailto:")):
        require((ROOT/href.split("#",1)[0]).is_file(),"Missing accompanying supplement: "+href)
for key in ["Khurgin2021","Gustafsson2012","Yazdi2015"]:
    require("ref-"+key in ids,"Missing new citation: "+key)
output=dict(passed=not errors,errors=errors,pdf_pages=len(reader.pages),pdf_layout_log_issues=tex_issues,
            pdf_word_bounds_issues=bounds,html_viewports=[r["width"] for r in browser],
            equations=formats["equations"],math_expressions=formats["math_expressions"],references=formats["references"],figures=1,correspondence_rows=len(rows),
            matched_library_hashes=len(cert["sourceHashes"]),frozen_commit=commit,original_checkout_unchanged=not status,
            source_hash_mismatches=mismatches,new_full_kernel_replay_performed=False,
            archived_declaration_and_correspondence_logs_inspected=True,
            kernel_replay_scope="Entire PrescribedExtinction aggregate import closure; same Lean kernel implementation",
            independent_semantic_review="Final independent audit unavailable; current correction review is AI-assisted; no human certification",
            independent_kernel_implementation_used=False,
            manuscript_source_sha256=formats["source_sha256"],
            identical_source_math_to_html=True if source_math==html_math else False,
            source_math_compared=len(source_math),changed_numbered_equations=changed_eq,
            vector_pdf_svg_labels_compared=len(figure_labels),pdf_internal_links_checked=len(pdf_destinations),
            main_and_aperture_theorem_text_unchanged=statement(original,"thm:main")==statement(current,"thm:main") and statement(original,"thm:aperture")==statement(current,"thm:aperture"),
            output_sha256={n:digest(ROOT/n) for n in ["paper.pdf","paper.html","theorem-correspondence.csv"]},
            visual_qa="All pages rendered; contact sheet and key full-size PDF pages and desktop/mobile formula/reference screenshots reviewed separately")
(ROOT/"review/validation.json").write_text(json.dumps(output,indent=2),encoding="utf-8")
print(json.dumps(output,indent=2))
if errors: raise SystemExit(1)
