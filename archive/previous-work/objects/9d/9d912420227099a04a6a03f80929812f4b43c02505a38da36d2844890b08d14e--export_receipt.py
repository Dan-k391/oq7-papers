from pathlib import Path
import hashlib,json,os,shutil,stat
SRC=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1")/"outputs/OQ7-GitHub-upload-20261013-0c32f324"
BASE=Path(r"C:\Users\Daniel\Documents\Codex\2026-10-13\audit-the-existing-oq7-project-do\outputs")
DST=BASE/SRC.name
def check(p):
    s=os.lstat(p)
    assert not(getattr(s,"st_file_attributes",0)&0x400 or stat.S_ISLNK(s.st_mode)),str(p)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
check(SRC)
for p in [BASE,*BASE.parents]:
    if p.exists():check(p)
DST.absolute().relative_to(BASE.absolute())
assert not DST.exists()
DST.mkdir(exist_ok=False)
for p in SRC.iterdir():
    check(p);assert p.is_file()
    q=DST/p.name;shutil.copy2(p,q);assert sha(p)==sha(q)
for line in (DST/"SHA256SUMS").read_text().splitlines():
    h,rel=line.split("  ",1);assert sha(DST/rel)==h
print(json.dumps({"exported_receipt":str(DST),"hashes_verified":True,"private_repository":"https://github.com/Dan-k391/oq7-prescribed-extinction","file_access_restoration":"user-confirmed disabled"},indent=2))

