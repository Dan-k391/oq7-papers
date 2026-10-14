from pathlib import Path, PurePosixPath
import datetime, hashlib, html, json, os, shutil, stat, zipfile
from html.parser import HTMLParser
from urllib.parse import unquote, urlparse

ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1")
OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324")
WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\s0c32f324")
BASE=ROOT/"outputs/OQ7-release-20261013-final-audit-59a36c60"
PRIORITY=ROOT/"outputs/OQ7-priority-20261013-7d4b21a9"

def regular(p):
    info=os.lstat(p)
    if getattr(info,"st_file_attributes",0)&0x400 or stat.S_ISLNK(info.st_mode):
        raise RuntimeError("Link/reparse point rejected: "+str(p))
def within(p,base):
    p.absolute().relative_to(base.absolute())
def walk(base):
    regular(base)
    files=[]
    for entry in sorted(base.iterdir()):
        regular(entry)
        if entry.is_dir(): files.extend(walk(entry))
        elif entry.is_file(): files.append(entry)
        else: raise RuntimeError("Nonregular entry "+str(entry))
    return files
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for block in iter(lambda:f.read(1024*1024),b""):h.update(block)
    return h.hexdigest()
def write_json(p,v):p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
def verify_manifest(base):
    result={}
    for line in (base/"SHA256SUMS").read_text(encoding="utf-8").splitlines():
        if not line.strip():continue
        expected,rel=line.split("  ",1)
        pos=PurePosixPath(rel)
        if pos.is_absolute() or ".." in pos.parts:raise RuntimeError("Unsafe manifest member "+rel)
        p=base/rel;regular(p);actual=sha(p)
        if actual!=expected:raise RuntimeError("Manifest mismatch "+str(p))
        result[rel]=actual
    return result

regular(ROOT);within(OUT,ROOT);within(WORK,ROOT)
walk(OUT)
ident=json.loads((OUT/"INPUT_IDENTITIES.json").read_text(encoding="utf-8"))
baseline=verify_manifest(BASE)
verify_manifest(PRIORITY)
for rel,expected in ident["existing_release"].items():
    if rel.startswith("release/"):
        origin=BASE/rel[len("release/"):];copied=OUT/rel
        if sha(origin)!=expected or sha(copied)!=expected:
            raise RuntimeError("Original/copy differs: "+rel)
    elif rel.startswith("project/"):
        origin=ROOT/rel[len("project/"):]
        regular(origin)
        if sha(origin)!=expected:raise RuntimeError("Historical original differs: "+rel)
    else:raise RuntimeError("Unmapped origin "+rel)
for p in walk(PRIORITY):
    q=OUT/"priority"/p.relative_to(PRIORITY)
    if sha(p)!=sha(q):raise RuntimeError("Priority evidence differs")
if sha(OUT/"frozen/paper.pdf")!=ident["frozen_pdf_sha256"]:raise RuntimeError("Frozen PDF changed")
if sha(OUT/"frozen/main.tex")!=ident["frozen_tex_sha256"]:raise RuntimeError("Frozen source changed")
if sha(OUT/"toolchain/lean-4.34.1-windows.zip")!=ident["lean_archive_sha256"]:raise RuntimeError("Pinned toolchain changed")
for rel,expected in {
"supplements/S2_FROZEN_SOURCE.zip":"d141a3ded8c2d9fe520c0c92ef82601f4e1b7ca3a5eb1580d018e33a8f4fd258",
"supplements/S2_FROZEN_SOURCE.bundle":"5a4e3a4623a910ee1f5993bc43b10da38d70125ef4aa74a22653b540b2db8479",
"supplements/S3_FROZEN_VERIFICATION_MANIFEST.json":"08aa0bd878602a9d112cf7d98d9bd7d22f9ae31c014f88a14396a292f18ec6a5"}.items():
    if sha(OUT/rel)!=expected:raise RuntimeError("Frozen supplement changed "+rel)
current=json.loads((OUT/"verification/CURRENT_VERIFICATION.json").read_text())
assert current["status"]=="PASS" and current["kernel_replay_exit_code"]==0
assert current["fresh_same_kernel_replay"] and not current["independent_kernel_implementation_used"]
assert current["library_source_modules_unchanged"]==378
for rel in ["supplements/S3_CURRENT_VERIFICATION.json","manuscript/reproducibility/current-verification.json"]:
    assert json.loads((OUT/rel).read_text())==current,rel
assert (OUT/"manuscript/reproducibility/AUDIT_PROVENANCE.md").read_bytes()==(OUT/"supplements/S4_AUDIT_PROVENANCE.md").read_bytes()
commands=[json.loads(x) for x in (OUT/"verification/COMMANDS.jsonl").read_text().splitlines() if x]
assert all(x["exit_code"]==0 for x in commands)
for command in commands:assert (OUT/"verification"/command["log"]).is_file()
preservation=json.loads((OUT/"MANUSCRIPT_PRESERVATION.json").read_text())
assert preservation["review_pdf_sha256"]==sha(OUT/"manuscript/paper.pdf")
assert preservation["review_tex_sha256"]==sha(OUT/"manuscript/main.tex")
assert preservation["all_math_environment_bodies_identical"]
assert preservation["mathematical_exposition_sections_3_to_9_identical"]

class Links(HTMLParser):
    def __init__(self):super().__init__();self.refs=[]
    def handle_starttag(self,tag,attrs):
        attrs=dict(attrs)
        if tag=="a" and "href" in attrs:self.refs.append(attrs["href"])
        if tag=="img" and "src" in attrs:self.refs.append(attrs["src"])
local_checks=[]
for p in walk(OUT/"manuscript"):
    if p.suffix.lower()!=".html":continue
    parser=Links();parser.feed(p.read_text(encoding="utf-8"))
    for ref in parser.refs:
        url=urlparse(ref)
        if url.scheme or not url.path:continue
        q=(p.parent/unquote(url.path)).resolve()
        within(q,OUT);regular(q)
        if not q.is_file():raise RuntimeError("Broken local link "+str(p)+" -> "+ref)
        local_checks.append({"page":p.relative_to(OUT).as_posix(),"href":ref,"target":q.relative_to(OUT).as_posix()})
write_json(OUT/"verification/FINAL_LOCAL_SUPPLEMENT_LINK_CHECK.json",{"status":"PASS","local_file_links_checked":len(local_checks),"links":local_checks})
qa=OUT/"verification/pdf-render"
qa.mkdir(exist_ok=False)
copied_qa=[]
for p in walk(WORK/"pdf-qa"):
    if p.suffix.lower()==".png":
        shutil.copy2(p,qa/p.name);copied_qa.append(p.name)
write_json(qa/"RENDER_EVIDENCE.json",{"pages":16,"files":copied_qa,"inspection":"All 16 page renders inspected; main theorem, figure, verification/disclosure and bibliography inspected at full-page resolution.","scope":"Current review PDF only","pdf_sha256":sha(OUT/"manuscript/paper.pdf")})
version=(OUT/"release/MANUSCRIPT_VERSION_CORRESPONDENCE.md").read_text(encoding="utf-8")
version+="\n## Final review revision in this package\n\nThe completed-audit release paper is preserved in frozen/paper.pdf (SHA-256 "+sha(OUT/"frozen/paper.pdf")+"). The checked review revision is manuscript/paper.pdf (SHA-256 "+sha(OUT/"manuscript/paper.pdf")+") and manuscript/main.tex (SHA-256 "+sha(OUT/"manuscript/main.tex")+"). Mathematical environment bodies and Sections 3–9 are preserved; the exact editorial diff and raw content identities are supplied. The release/evidence/ originals retain the historical source/version record.\n\nThe final revision corrects the Sounas 2017 attribution using the existing source-verified priority report, links that report's limitations, and adds AI-assistance disclosure. It adds no theorem, stronger scope, new research or novelty conclusion.\n"
(OUT/"MANUSCRIPT_VERSION_CORRESPONDENCE.md").write_text(version,encoding="utf-8")
shutil.copy2(OUT/"priority/REMAINING_PRIORITY_QUESTIONS.md",OUT/"REMAINING_PRIORITY_QUESTIONS.md")
# Index text uses package-relative links for the current, rather than historical, version.
index="""# OQ7 final review package

The exact audited commit is 686402a6c2d63820828729cc7ab02504632e3fe7. The frozen originals are preserved. This package retains the compact prescribed-extinction theorem and the completed final audit evidence; it adds no research.

| Deliverable | File |
|---|---|
| Checked anonymous review paper and source | [paper.pdf](manuscript/paper.pdf), [main.tex](manuscript/main.tex), [bibliography](manuscript/references.bib) |
| Frozen completed-audit release paper | [frozen paper](frozen/paper.pdf), [frozen source](frozen/main.tex) |
| S1: claim-to-code correspondence | [statement and scope](supplements/S1_THEOREM_CORRESPONDENCE.md), [CSV](supplements/S1_THEOREM_CORRESPONDENCE.csv), [HTML](supplements/S1_THEOREM_CORRESPONDENCE.html) |
| S2: exact frozen source repository | [source archive](supplements/S2_FROZEN_SOURCE.zip), [complete Git bundle](supplements/S2_FROZEN_SOURCE.bundle) |
| S3: immutable manifest and current checks | [frozen manifest](supplements/S3_FROZEN_VERIFICATION_MANIFEST.json), [current verification](supplements/S3_CURRENT_VERIFICATION.json) |
| S4: audit provenance | [provenance](supplements/S4_AUDIT_PROVENANCE.md) |
| Exact source/dependency pins and toolchain | [pin/source identities](verification/PIN_AND_SOURCE_IDENTITIES.json), [dependency snapshots](release/dependency-sources/PINNED_DEPENDENCIES.json), [Lean 4.34.1 archive](toolchain/lean-4.34.1-windows.zip) |
| Preserved final audit and preceding audit | [final](release/evidence/AUDIT_REPORT_686402a.md), [preceding](release/evidence/preceding/AUDIT_REPORT_5a8350d.md) |
| Current audit and version map | [final package audit](FINAL_REVIEW_AUDIT.md), [version dispositions](VERSION_VERIFICATION_DISPOSITION.md), [manuscript correspondence](MANUSCRIPT_VERSION_CORRESPONDENCE.md) |
| Regenerated checking outputs | [theorem type](FINAL_THEOREM_TYPE.txt), [axioms](FINAL_AXIOMS.txt), [fresh replay](KERNEL_REPLAY.log), [exact commands](verification/COMMANDS.jsonl) |
| Reproduction | [commands and limitations](REPRODUCE.md), [portable differences](release/RELEASE_DIFFERENCES.md) |
| Priority | [existing comparison](priority/TARGETED_PRIORITY_REPORT.md), [remaining questions](REMAINING_PRIORITY_QUESTIONS.md) |
| Author and assistance disclosure | [author information](AUTHOR_INFORMATION.md), manuscript Section 10 |
| Content and packaging identity | [SHA256SUMS](SHA256SUMS), [package status](FINAL_PACKAGE_STATUS.json) |

The old thickness checkpoint is uncompiled. The 43-authored-theorem finite-port source package is not recovered; neither is substituted for the final Maxwell source. The main final theorem and its current replay use only propext, Classical.choice and Quot.sound.

The same-kernel fresh replay passes. The main-statement semantic and ordinary mathematical reviews are AI-assisted evidence with their recorded scope. No completed human peer review or independently implemented kernel checker is claimed. The existing bounded priority investigation does not establish first priority.

This is an anonymous review copy: author name, affiliation and corresponding-author metadata have not been supplied. Named journal-submission metadata remains incomplete. No preprint upload, publication or journal submission has occurred.

The complete archive includes the pinned compiler and dependency source/Git archives. The email-sized packet omits those large binary/source snapshots and says so explicitly; it includes the paper, source, frozen proof repository, S1–S4, reports, regenerated logs and instructions. Email transmission, if made using the user's authorized recipient and selected sender, is recorded separately from this immutable package.
"""
(OUT/"RELEASE_INDEX.md").write_text(index,encoding="utf-8")
status={
"sealed_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
"target":"compact prescribed-extinction Maxwell supremum",
"audited_commit":ident["source_commit"],"portable_commit":ident["portable_commit"],
"preserved_original_manifest_files":len(baseline),
"frozen_source_recovered":True,
"all_378_mathematical_modules_byte_identical":True,
"pinned_dependencies_unchanged":True,"current_cached_build_and_audit_programs":"PASS",
"prior_clean_build":"preserved completed evidence; not rerun from source in this finalization",
"same_kernel_fresh_replay":{"status":"PASS","exit_code":0,"elapsed_seconds":current["kernel_replay_elapsed_seconds"]},
"main_theorem_axioms":current["main_dependency_axioms"],
"main_statement_semantic_review":"completed AI-assisted final-commit evidence",
"ordinary_mathematical_review":"completed AI-assisted review, version/scope recorded",
"every_intermediate_manuscript_line_verified":False,
"human_peer_review":"not established",
"independently_implemented_kernel_checker":"not performed",
"first_priority":"unresolved; existing bounded report retained; no new investigation",
"old_thickness_checkpoint":"uncompiled historical evidence",
"43_theorem_finite_port_source":"not recovered",
"review_pdf_sha256":sha(OUT/"manuscript/paper.pdf"),
"author_metadata":"anonymous; named submission metadata incomplete",
"publication_preprint_journal_submission":"not performed",
"email":{"recipient_authorized":"denialk391@gmail.com","status_at_sealing":"not sent; sender choice unresolved","receipt":"separate from sealed package"}
}
write_json(OUT/"FINAL_PACKAGE_STATUS.json",status)
write_json(OUT/"verification/ORIGINALS_RECHECKED_AT_SEAL.json",{"status":"PASS","existing_release_manifest_files":len(baseline),"preserved_input_identity_records":len(ident["existing_release"]),"priority_originals_preserved":True,"frozen_pdf_source_preserved":True,"no_links_followed":True,"source_root":str(ROOT)})
files=walk(OUT)
ids={p.relative_to(OUT).as_posix():sha(p) for p in files if p.name!="SHA256SUMS" or p.parent!=OUT}
(OUT/"SHA256SUMS").write_text("".join(h+"  "+r+"\n" for r,h in sorted(ids.items())),encoding="utf-8")
verified=verify_manifest(OUT)
assert verified==ids
print("Sealed package manifest:",len(ids),"files; originals, links, frozen source and current status PASS",flush=True)

COMPLETE=OUT.parent/"OQ7-final-review-complete-20261013-0c32f324.zip"
SMALL=OUT.parent/"OQ7-review-materials-20261013-0c32f324.zip"
# Full content archive preserves all source/audit/toolchain bytes.
files=walk(OUT)
with zipfile.ZipFile(COMPLETE,"x",allowZip64=True,compresslevel=6) as z:
    for p in files:
        rel=p.relative_to(OUT).as_posix()
        method=zipfile.ZIP_STORED if p.suffix.lower() in {".zip",".bundle",".pdf",".png",".gz"} else zipfile.ZIP_DEFLATED
        z.write(p,rel,compress_type=method)
print("Complete source-and-audit archive created:",COMPLETE.stat().st_size,"bytes",flush=True)

# Smaller review archive omits large pins/binary snapshots and redundant historical source copies.
excluded_prefixes=("toolchain/","release/dependency-sources/","release/manuscript/","verification/pdf-render/")
selected=[]
for p in files:
    rel=p.relative_to(OUT).as_posix()
    if rel=="SHA256SUMS" or rel.startswith(excluded_prefixes):continue
    selected.append((p,rel))
small_note="""# Email review packet scope

This packet includes the review PDF/source, S1–S4, frozen Lean source/Git bundle, portable release source, current type/axiom/auditor/fresh-replay logs, completed audit reports, ordinary review, historical version map and the existing targeted priority report.

It omits the 850 MB pinned Windows compiler, the nine dependency source/Git snapshots, redundant release/manuscript/ copies and PDF-render PNGs. These are included in the complete local source-and-audit archive. The main REPRODUCE.md and RELEASE_INDEX.md describe that complete package. Links to omitted snapshot files require the complete archive. This packet's SHA256SUMS covers its own included members only.

No human peer review, independent-kernel checker or established first priority is claimed. This is an anonymous review copy, not a named journal submission.
"""
note_bytes=small_note.encode("utf-8")
small_ids={rel:sha(p) for p,rel in selected}
small_ids["EMAIL_PACKET_SCOPE.md"]=hashlib.sha256(note_bytes).hexdigest()
with zipfile.ZipFile(SMALL,"x",allowZip64=True,compresslevel=6) as z:
    for p,rel in selected:
        method=zipfile.ZIP_STORED if p.suffix.lower() in {".zip",".bundle",".pdf",".gz"} else zipfile.ZIP_DEFLATED
        z.write(p,rel,compress_type=method)
    z.writestr("EMAIL_PACKET_SCOPE.md",note_bytes,compress_type=zipfile.ZIP_DEFLATED)
    z.writestr("SHA256SUMS","".join(h+"  "+r+"\n" for r,h in sorted(small_ids.items())),compress_type=zipfile.ZIP_DEFLATED)
print("Email review packet created:",SMALL.stat().st_size,"bytes",flush=True)

def verify_zip(path,expected_ids):
    with zipfile.ZipFile(path) as z:
        names=z.namelist()
        assert len(names)==len(set(names))
        for name in names:
            member=PurePosixPath(name)
            assert not member.is_absolute() and ".." not in member.parts,name
        got={}
        for name in names:
            if name=="SHA256SUMS":continue
            h=hashlib.sha256()
            with z.open(name) as f:
                for block in iter(lambda:f.read(1024*1024),b""):h.update(block)
            got[name]=h.hexdigest()
        assert got==expected_ids,"Archive content hash mismatch "+str(path)
        archive_manifest=z.read("SHA256SUMS").decode("utf-8")
        archive_ids=dict((rel,h) for h,rel in (line.split("  ",1) for line in archive_manifest.splitlines() if line))
        assert archive_ids==expected_ids
    return {"path":str(path),"size_bytes":path.stat().st_size,"sha256":sha(path),"content_members_verified":len(expected_ids),"all_member_sha256_verified":True}
complete_record=verify_zip(COMPLETE,ids)
small_record=verify_zip(SMALL,small_ids)
assert SMALL.stat().st_size+(OUT/"manuscript/paper.pdf").stat().st_size<18*1024*1024,"Email attachments unexpectedly large"
for record in [complete_record,small_record]:
    p=Path(record["path"])
    p.with_suffix(p.suffix+".sha256").write_text(record["sha256"]+"  "+p.name+"\n",encoding="utf-8")
record={"status":"PASS","complete":complete_record,"email_review_packet":small_record,"source_manifest_file_sha256":sha(OUT/"SHA256SUMS")}
write_json(OUT.parent/"OQ7-final-review-ARCHIVE_CHECK-0c32f324.json",record)
print(json.dumps(record,indent=2),flush=True)

