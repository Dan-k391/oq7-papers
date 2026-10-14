from pathlib import Path
import hashlib,json,os,shutil,stat
SOURCE=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324")
TARGET_BASE=Path(r"C:\Users\Daniel\Documents\Codex\2026-10-13\audit-the-existing-oq7-project-do\outputs")
TARGET=TARGET_BASE/SOURCE.name
def regular(p):
    st=os.lstat(p)
    assert not(getattr(st,"st_file_attributes",0)&0x400 or stat.S_ISLNK(st.st_mode)),str(p)
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
    return h.hexdigest()
def copy_tree(src,dst):
    regular(src);assert not dst.exists(),str(dst)
    dst.absolute().relative_to(TARGET_BASE.absolute())
    dst.mkdir(exist_ok=False)
    for p in src.iterdir():
        regular(p)
        if p.is_dir():copy_tree(p,dst/p.name)
        elif p.is_file():shutil.copy2(p,dst/p.name)
        else:raise RuntimeError(str(p))
for p in [TARGET_BASE,*TARGET_BASE.parents]:
    if p.exists():regular(p)
if not TARGET_BASE.exists():TARGET_BASE.mkdir(parents=True,exist_ok=False)
assert not TARGET.exists(),"Unique export directory unexpectedly exists"
copy_tree(SOURCE,TARGET)
records=[]
for line in (SOURCE/"SHA256SUMS").read_text().splitlines():
    expected,rel=line.split("  ",1)
    p=TARGET/rel;regular(p)
    assert sha(p)==expected,rel
assert sha(TARGET/"SHA256SUMS")==sha(SOURCE/"SHA256SUMS")
for name in [
"OQ7-final-review-complete-20261013-0c32f324.zip",
"OQ7-final-review-complete-20261013-0c32f324.zip.sha256",
"OQ7-review-email-20261013-0c32f324.zip",
"OQ7-review-email-20261013-0c32f324.zip.sha256",
"OQ7-final-review-ARCHIVE_CHECK-0c32f324.json"
]:
    src=SOURCE.parent/name;dst=TARGET_BASE/name
    regular(src);assert not dst.exists()
    shutil.copy2(src,dst)
    assert sha(src)==sha(dst),name
    records.append({"path":str(dst),"sha256":sha(dst),"size_bytes":dst.stat().st_size})
record={"status":"PASS","exported_package":str(TARGET),"all_235_manifest_files_verified":True,"manifest_sha256":sha(TARGET/"SHA256SUMS"),"archives_and_sidecars":records,"email_sent":False,"email_sender_choice_pending":True}
p=TARGET_BASE/"OQ7-final-review-EXPORT_CHECK-0c32f324.json";assert not p.exists()
p.write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
print(json.dumps(record,indent=2))

