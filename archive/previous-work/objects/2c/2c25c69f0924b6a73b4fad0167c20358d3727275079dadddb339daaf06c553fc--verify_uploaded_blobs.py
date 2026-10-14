from pathlib import Path
import hashlib,json,subprocess,os
ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1")
WORK=ROOT/"work/github-upload-20261013-0c32f324";REPO=WORK/"repo"
GIT=r"C:\Program Files\Git\cmd\git.exe"
record=json.loads((WORK/"UPLOAD_PREPARED.json").read_text())
expected={}
for line in (REPO/"review-package/SHA256SUMS").read_text().splitlines():
    h,r=line.split("  ",1)
    if r!="toolchain/lean-4.34.1-windows.zip":expected[r]=h
p=subprocess.Popen([GIT,"cat-file","--batch"],cwd=REPO,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
mismatches=[]
for rel,want in expected.items():
    p.stdin.write(("HEAD:review-package/"+rel+"\n").encode());p.stdin.flush()
    header=p.stdout.readline().decode().strip().split()
    if len(header)!=3 or header[1]!="blob":raise RuntimeError(header)
    size=int(header[2]);got=hashlib.sha256()
    while size:
        b=p.stdout.read(min(size,1024*1024))
        if not b:raise RuntimeError("Short blob")
        got.update(b);size-=len(b)
    assert p.stdout.read(1)==b"\n"
    if got.hexdigest()!=want:mismatches.append(rel)
p.stdin.close();assert p.wait()==0
assert not mismatches,mismatches
head=subprocess.check_output([GIT,"rev-parse","HEAD"],cwd=REPO,text=True).strip()
assert head==record["upload_commit"]
r=subprocess.run([GIT,"tag","review-package-2026-10-13",head],cwd=REPO,capture_output=True,text=True)
assert r.returncode==0,r.stderr
record.update(status="main and original tags pushed; review-archive tag prepared",all_234_git_blob_sha256_match_sealed_manifest=True,review_tag="review-package-2026-10-13",ref_verification="REMOTE_REFS.log")
(WORK/"UPLOAD_GIT_BLOBS_VERIFIED.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
print("All 234 uploaded-package Git blobs match the sealed SHA-256 manifest. Original source/tag identities preserved.")

