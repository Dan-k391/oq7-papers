from pathlib import Path
import datetime, hashlib, json, os, shutil, stat, subprocess
ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1"); OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324"); WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\s0c32f324")
BASE=ROOT/"outputs/OQ7-release-20261013-final-audit-59a36c60"
PRIORITY=ROOT/"outputs/OQ7-priority-20261013-7d4b21a9"
GIT=Path(r"C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd\git.exe")
env=dict(os.environ);env.update(GIT_CONFIG_NOSYSTEM="1",GIT_CONFIG_GLOBAL="NUL",GIT_OPTIONAL_LOCKS="0",GIT_CONFIG_COUNT="1",GIT_CONFIG_KEY_0="core.longpaths",GIT_CONFIG_VALUE_0="true",PYTHONUTF8="1")
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda:f.read(1024*1024),b""):h.update(chunk)
    return h.hexdigest()
def regular(p):
    info=os.lstat(p)
    if getattr(info,"st_file_attributes",0)&0x400 or stat.S_ISLNK(info.st_mode):raise RuntimeError("Reparse/link not followed: "+str(p))
def copy_tree(src,dst):
    regular(src);dst.mkdir(parents=True,exist_ok=False)
    for item in src.iterdir():
        regular(item)
        if item.is_dir():copy_tree(item,dst/item.name)
        elif item.is_file():shutil.copy2(item,dst/item.name)
        else:raise RuntimeError("Nonregular entry: "+str(item))
def copy_file(src,dst):
    regular(src);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
old_ids={}
for line in (BASE/"SHA256SUMS").read_text(encoding="utf-8").splitlines():
    expected,rel=line.split("  ",1);p=BASE/rel;regular(p)
    actual=sha(p)
    if actual!=expected:raise RuntimeError("Existing release hash differs: "+rel)
    old_ids["release/"+rel]=actual
old_ids["release/SHA256SUMS"]=sha(BASE/"SHA256SUMS")
print("Existing release manifest verified:",len(old_ids),"files",flush=True)
copy_tree(BASE,OUT/"release")
copy_tree(PRIORITY,OUT/"priority")
copy_tree(BASE/"manuscript",OUT/"manuscript")
copy_file(BASE/"manuscript/paper.pdf",OUT/"frozen/paper.pdf")
copy_file(BASE/"manuscript/main.tex",OUT/"frozen/main.tex")
historical=[
("outputs/oq7-paper1-publication/MATHEMATICAL_CONSISTENCY.md","reviews/MATHEMATICAL_CONSISTENCY_ORIGINAL.md"),
("outputs/oq7-paper1-publication/PUBLICATION_ISSUES.md","reviews/PUBLICATION_ISSUES_ORIGINAL.md"),
("outputs/OQ7-audit-20261013-a89f0ec7-128b-4db6-ae6a-40d4bf427076/VERSION_AND_AUDIT_MAP.md","historical/VERSION_AND_AUDIT_MAP_INVENTORY_STAGE.md"),
("outputs/oq7/sources/original-checkpoint.md","historical/SCALAR_THICKNESS_CHECKPOINT.md")]
for src,dst in historical:
    copy_file(ROOT/src,OUT/dst);old_ids["project/"+src]=sha(ROOT/src)
(OUT/"verification").mkdir()
(WORK/"repo").parent.mkdir(exist_ok=True)
print("Cloning the separate portable revision",flush=True)
r=subprocess.run([str(GIT),"clone",str(BASE/"portable-release.bundle"),str(WORK/"repo")],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(OUT/"verification/prepare-clone.log").write_bytes(r.stdout)
if r.returncode:raise RuntimeError("Clone failed")
r=subprocess.run([str(GIT),"rev-parse","HEAD"],cwd=WORK/"repo",env=env,capture_output=True,text=True)
if r.stdout.strip()!="0bdf00f9b75b43194436f9536b1bf09463fd5a5d":raise RuntimeError("Portable commit mismatch")
print("Copying the previously verified build cache into the isolated checkout",flush=True)
copy_tree(ROOT/"work/r59a36c60/lean/.lake",WORK/"repo/.lake")
print("Build-cache copy complete",flush=True)
toolzip=ROOT/"work/a89f0ec7/tools/lean-4.34.1-windows.zip"
expected="457698d4e2132243e899ff32178d7ae63c16431d09ed9ad524d859c3581992af"
if sha(toolzip)!=expected:raise RuntimeError("Pinned Lean archive hash mismatch")
copy_file(toolzip,OUT/"toolchain/lean-4.34.1-windows.zip")
(OUT/"INPUT_IDENTITIES.json").write_text(json.dumps(dict(source_root=str(ROOT),existing_release=old_ids,source_commit="686402a6c2d63820828729cc7ab02504632e3fe7",portable_commit="0bdf00f9b75b43194436f9536b1bf09463fd5a5d",frozen_pdf_sha256=sha(OUT/"frozen/paper.pdf"),frozen_tex_sha256=sha(OUT/"frozen/main.tex"),lean_archive_sha256=expected),indent=2),encoding="utf-8")
print("PREPARATION_COMPLETE",flush=True)

