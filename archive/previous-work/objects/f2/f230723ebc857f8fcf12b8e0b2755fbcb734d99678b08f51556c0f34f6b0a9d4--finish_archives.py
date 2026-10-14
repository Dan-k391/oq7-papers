from pathlib import Path, PurePosixPath
import hashlib,json,os,stat,zipfile
ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1");OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324")
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for block in iter(lambda:f.read(1024*1024),b""):h.update(block)
    return h.hexdigest()
def walk(base):
    attr=os.lstat(base)
    assert not(getattr(attr,"st_file_attributes",0)&0x400 or stat.S_ISLNK(attr.st_mode)),str(base)
    result=[]
    for p in sorted(base.iterdir()):
        attr=os.lstat(p)
        assert not(getattr(attr,"st_file_attributes",0)&0x400 or stat.S_ISLNK(attr.st_mode)),str(p)
        if p.is_dir():result.extend(walk(p))
        elif p.is_file():result.append(p)
        else:raise RuntimeError(str(p))
    return result
def manifest(p):
    return dict((r,h) for h,r in (s.split("  ",1) for s in p.read_text().splitlines() if s))
ids=manifest(OUT/"SHA256SUMS")
for rel,h in ids.items():assert sha(OUT/rel)==h,rel
COMPLETE=OUT.parent/"OQ7-final-review-complete-20261013-0c32f324.zip"
SMALL=OUT.parent/"OQ7-review-email-20261013-0c32f324.zip"
prefixes=("toolchain/","release/dependency-sources/","release/manuscript/","verification/pdf-render/")
omit={"SHA256SUMS","release/frozen/OQ7-complete-physical-theorem11-source.zip","release/frozen/OQ7-complete-physical-theorem11.bundle","release/portable-release.bundle"}
selected=[(p,p.relative_to(OUT).as_posix()) for p in walk(OUT) if p.relative_to(OUT).as_posix() not in omit and not p.relative_to(OUT).as_posix().startswith(prefixes)]
note="""# Email review packet scope

This packet includes the review PDF/source, S1–S4, exact frozen Lean source archive/Git bundle, portable release source archive, current type/axiom/auditor/fresh-replay logs, completed audit reports and programs, ordinary review, historical version map and the existing targeted priority report.

It omits the 850 MB pinned Windows compiler, all nine dependency source/Git snapshots, redundant release/manuscript/ copies, PDF-render PNGs, redundant release/frozen/ source archive/bundle copies and the portable Git bundle. The same exact audited source/Git bundle remain in supplements/ and manuscript/reproducibility/. The portable source remains in release/portable-source.zip.

All omitted items are included in the complete local source-and-audit archive. The main REPRODUCE.md and RELEASE_INDEX.md describe that complete package. Links to omitted snapshot files require the complete archive. This packet's SHA256SUMS covers its own included members only.

No human peer review, independent-kernel checker or established first priority is claimed. This is an anonymous review copy, not a named journal submission.
""".encode("utf-8")
small_ids={rel:ids[rel] for _,rel in selected}
small_ids["EMAIL_PACKET_SCOPE.md"]=hashlib.sha256(note).hexdigest()
with zipfile.ZipFile(SMALL,"x",allowZip64=True,compresslevel=6) as z:
    for p,rel in selected:
        method=zipfile.ZIP_STORED if p.suffix.lower() in {".zip",".bundle",".pdf",".gz"} else zipfile.ZIP_DEFLATED
        z.write(p,rel,compress_type=method)
    z.writestr("EMAIL_PACKET_SCOPE.md",note,compress_type=zipfile.ZIP_DEFLATED)
    z.writestr("SHA256SUMS","".join(h+"  "+r+"\n" for r,h in sorted(small_ids.items())),compress_type=zipfile.ZIP_DEFLATED)
assert SMALL.stat().st_size+(OUT/"manuscript/paper.pdf").stat().st_size<18*1024*1024
def check(path,expected):
    with zipfile.ZipFile(path) as z:
        names=z.namelist();assert len(names)==len(set(names))
        actual={}
        for name in names:
            p=PurePosixPath(name)
            assert not p.is_absolute() and ".." not in p.parts
            if name=="SHA256SUMS":continue
            h=hashlib.sha256()
            with z.open(name) as f:
                for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
            actual[name]=h.hexdigest()
        assert actual==expected
        packed=dict((r,h) for h,r in (s.split("  ",1) for s in z.read("SHA256SUMS").decode("utf-8").splitlines() if s))
        assert packed==expected
    return {"path":str(path),"filename":path.name,"size_bytes":path.stat().st_size,"sha256":sha(path),"content_members_verified":len(expected),"all_member_sha256_verified":True}
records=[check(COMPLETE,ids),check(SMALL,small_ids)]
for item in records:
    p=Path(item["path"]);p.with_suffix(p.suffix+".sha256").write_text(item["sha256"]+"  "+p.name+"\n",encoding="utf-8")
result={"status":"PASS","complete":records[0],"email_review_packet":records[1],"source_manifest_file_sha256":sha(OUT/"SHA256SUMS"),
"oversized_trial_packet":{"filename":"OQ7-review-materials-20261013-0c32f324.zip","bytes":27073486,"status":"preserved packaging trial; not selected for email or export"},
"attachment_size_check":"selected review packet plus separate PDF under 18 MiB before MIME encoding"}
(OUT.parent/"OQ7-final-review-ARCHIVE_CHECK-0c32f324.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
print(json.dumps(result,indent=2))

