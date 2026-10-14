from pathlib import Path, PurePosixPath
import argparse,csv,hashlib,os,shutil,stat
ROOT=Path(__file__).resolve().parents[1]
a=argparse.ArgumentParser();a.add_argument("--prefix",required=True);a.add_argument("--destination",required=True);args=a.parse_args()
prefix=PurePosixPath(args.prefix.replace("\\","/"))
if prefix.is_absolute() or ".." in prefix.parts:raise SystemExit("Unsafe prefix")
dest=Path(args.destination).absolute()
if dest.exists():raise SystemExit("Destination must be new; no originals overwritten")
records=list(csv.DictReader((ROOT/"archive/PREVIOUS_WORK_MAP.csv").open(encoding="utf-8")))
selected=[r for r in records if r["original_path"]==str(prefix) or r["original_path"].startswith(str(prefix)+"/")]
if not selected:raise SystemExit("No inventoried origin matches this prefix")
dest.mkdir(parents=True,exist_ok=False);count=0;omitted=0
for r in selected:
    if r["disposition"] in {"excluded-generated-or-vendor","existing-private-asset"}:omitted+=1;continue
    src=ROOT/r["stored_path"]
    st=os.lstat(src)
    if getattr(st,"st_file_attributes",0)&0x400 or stat.S_ISLNK(st.st_mode):raise SystemExit("Link not restored")
    rel=PurePosixPath(r["original_path"]).relative_to(prefix)
    if not rel.parts:rel=PurePosixPath(src.name)
    dst=dest/str(rel);dst.absolute().relative_to(dest)
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
    if hashlib.sha256(dst.read_bytes()).hexdigest()!=r["sha256"]:raise SystemExit("Restored hash mismatch")
    count+=1
print("Restored",count,"exact authored/evidence files;",omitted,"external/generated files omitted.")
