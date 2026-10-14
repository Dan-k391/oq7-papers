from pathlib import Path
import hashlib,json,re,shutil
OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324");WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\s0c32f324")
supp=OUT/"supplements";supp.mkdir(exist_ok=True)
copies=[
("manuscript/theorem-correspondence.csv","supplements/S1_THEOREM_CORRESPONDENCE.csv"),
("manuscript/theorem-correspondence.html","supplements/S1_THEOREM_CORRESPONDENCE.html"),
("release/frozen/OQ7-complete-physical-theorem11-source.zip","supplements/S2_FROZEN_SOURCE.zip"),
("release/frozen/OQ7-complete-physical-theorem11.bundle","supplements/S2_FROZEN_SOURCE.bundle"),
("release/manuscript/reproducibility/manifest.json","supplements/S3_FROZEN_VERIFICATION_MANIFEST.json"),
("release/AUDIT_PROVENANCE.md","reviews/COMPLETED_AUDIT_PROVENANCE_ORIGINAL.md")]
for src,dst in copies:shutil.copy2(OUT/src,OUT/dst)
shutil.copy2(OUT/"supplements/S1_THEOREM_CORRESPONDENCE.md",OUT/"CLAIM_TO_CODE.md")
shutil.copy2(OUT/"supplements/S4_AUDIT_PROVENANCE.md",OUT/"AUDIT_PROVENANCE.md")
tex=(OUT/"manuscript/main.tex").read_text(encoding="utf-8")
bib=(OUT/"manuscript/references.bib").read_text(encoding="utf-8")
keys=re.findall(r"@\w+\{\s*([^,\s]+)",bib)
cited=[key for group in re.findall(r"\\cite[a-z]*\{([^}]+)\}",tex) for key in group.split(",")]
labels=re.findall(r"\\label\{([^}]+)\}",tex);refs=re.findall(r"\\(?:eqref|ref)\{([^}]+)\}",tex)
missing_cites=set(cited)-set(keys);missing_refs=set(refs)-set(labels)
if missing_cites or missing_refs or len(labels)!=len(set(labels)):raise RuntimeError("Bibliography/cross-reference mismatch")
aux=(OUT/"manuscript/build/main.aux").read_text(encoding="utf-8")
if re.search(r"LaTeX Warning|Overfull|undefined references|Citation.*undefined",(OUT/"manuscript/build/main.log").read_text(encoding="utf-8"),re.I):raise RuntimeError("TeX presentation warning requires inspection")
html=(OUT/"manuscript/paper.html").read_text(encoding="utf-8")
from html.parser import HTMLParser
class Links(HTMLParser):
    def __init__(self):super().__init__();self.ids=[];self.hrefs=[]
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if "id" in a:self.ids.append(a["id"])
        if tag=="a" and "href" in a:self.hrefs.append(a["href"])
p=Links();p.feed(html)
if len(p.ids)!=len(set(p.ids)):raise RuntimeError("Duplicate HTML id")
missing=[href for href in p.hrefs if href.startswith("#") and href[1:] not in p.ids]
if missing:raise RuntimeError("Missing HTML anchors")
broken_local=[]
for href in p.hrefs:
    if "://" not in href and not href.startswith(("#","data:","mailto:")):
        local=(OUT/"manuscript"/href.split("#")[0])
        if not local.exists():broken_local.append(href)
if broken_local:raise RuntimeError("Missing manuscript supplement link: "+str(broken_local))
science_start=r"\section{Maxwell model, material class, and cross sections}"
science_end=r"\section{Formal verification"
before=(OUT/"frozen/main.tex").read_text(encoding="utf-8")
if before[before.index(science_start):before.index(science_end)]!=tex[tex.index(science_start):tex.index(science_end)]:raise RuntimeError("Mathematical exposition changed")
pat=r"\\begin\{(theorem|lemma|proposition|corollary|proof|equation)\}.*?\\end\{\1\}"
if [m.group(0) for m in re.finditer(pat,before,re.S)]!=[m.group(0) for m in re.finditer(pat,tex,re.S)]:raise RuntimeError("Math environment changed")
record=dict(bibliography_entries=len(keys),distinct_citations=len(set(cited)),uncited_entries=sorted(set(keys)-set(cited)),missing_citations=[],missing_references=[],unique_tex_labels=len(labels),html_internal_links=sum(h.startswith("#") for h in p.hrefs),html_missing_targets=[],html_duplicate_ids=[],local_manuscript_links_resolve=True,equation_count=len(re.findall(r"\\begin\{equation\}",tex)),mathematical_environment_bodies_preserved=True,mathematical_sections_3_to_9_preserved=True,author_field="blank; anonymous review",pdf_visual_check="All 16 page renders examined; main theorem, figure, formal-status/disclosure and references inspected at full-page resolution",bibliography_verification_scope="Static citation/metadata consistency against existing supplied records and completed priority registry; no new literature search",new_research=False)
(OUT/"verification/DOCUMENT_AND_BIBLIOGRAPHY_CHECK.json").write_text(json.dumps(record,indent=2),encoding="utf-8")
(OUT/"AUTHOR_INFORMATION.md").write_text("""# Author and disclosure status

The frozen and review manuscripts have blank author fields. No author name, affiliation, ORCID or corresponding-author email has been supplied for insertion. The review copy is anonymous. Local directory names and connected Gmail profiles are not treated as authorship evidence.

The manuscript contains an explicit disclosure of AI assistance for this release's document preparation, source-to-claim comparison, compilation checks and focused priority analysis. The original mathematical/semantic reports retain their own AI-assisted attributions and exact reviewed versions.

This package can be provided for review. It is not described as ready for named journal submission while author details, author responsibility confirmation and the chosen venue's requirements remain unspecified. No human peer review or independent-kernel checking category is fabricated.
""",encoding="utf-8")
print("DOCUMENT_AND_BIBLIOGRAPHY_CHECK_PASS",json.dumps(record))

