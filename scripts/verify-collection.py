from pathlib import Path
import csv,hashlib,json,os,stat
ROOT=Path(__file__).resolve().parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
    return h.hexdigest()
for line in (ROOT/"SHA256SUMS").read_text().splitlines():
    h,rel=line.split("  ",1);p=ROOT/rel
    s=os.lstat(p)
    if getattr(s,"st_file_attributes",0)&0x400 or stat.S_ISLNK(s.st_mode):raise SystemExit("Link rejected "+rel)
    if sha(p)!=h:raise SystemExit("Hash mismatch "+rel)
checked=set();origins=0
for r in csv.DictReader((ROOT/"archive/PREVIOUS_WORK_MAP.csv").open(encoding="utf-8")):
    if r["disposition"] in {"excluded-generated-or-vendor","existing-private-asset"}:continue
    rel=r["stored_path"];p=ROOT/rel
    if (rel,r["sha256"]) not in checked:
        if sha(p)!=r["sha256"]:raise SystemExit("Previous work differs "+r["original_path"])
        checked.add((rel,r["sha256"]))
    origins+=1
for r in csv.DictReader((ROOT/"archive/RELOCATION_MAP.csv").open(encoding="utf-8")):
    if sha(ROOT/r["new_path"])!=r["sha256"]:raise SystemExit("Relocated baseline differs "+r["old_path"])
print("PASS: repository manifest, all relocated baseline bytes, and",origins,"prior origin records verified.")
