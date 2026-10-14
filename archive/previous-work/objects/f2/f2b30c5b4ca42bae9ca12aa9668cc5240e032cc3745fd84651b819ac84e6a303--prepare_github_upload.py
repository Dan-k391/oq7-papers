from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess
ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1");SOURCE=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324")
WORK=ROOT/"work/github-upload-20261013-0c32f324"
REPO=WORK/"repo";GIT=Path(r"C:\Program Files\Git\cmd\git.exe")
REMOTE="https://github.com/Dan-k391/oq7-prescribed-extinction.git"
WORK.mkdir(exist_ok=False)
ENV=dict(os.environ)
ENV.update(GIT_TERMINAL_PROMPT="0",GCM_INTERACTIVE="Never",GIT_CONFIG_NOSYSTEM="1",GIT_CONFIG_GLOBAL="NUL",GIT_CONFIG_COUNT="2",GIT_CONFIG_KEY_0="core.longpaths",GIT_CONFIG_VALUE_0="true",GIT_CONFIG_KEY_1="core.autocrlf",GIT_CONFIG_VALUE_1="false")
def cmd(args,cwd=WORK):
    r=subprocess.run([str(GIT),*args],cwd=cwd,env=ENV,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log={"argv":[str(GIT),*args],"cwd":str(cwd),"exit_code":r.returncode,"output":r.stdout.decode("utf-8",errors="replace")}
    with (WORK/"LOCAL_COMMANDS.jsonl").open("a",encoding="utf-8") as f:f.write(json.dumps(log)+"\n")
    if r.returncode:raise RuntimeError(log)
    return log["output"].strip()
def regular(p):
    s=os.lstat(p)
    if getattr(s,"st_file_attributes",0)&0x400 or stat.S_ISLNK(s.st_mode):raise RuntimeError("Link rejected "+str(p))
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
    return h.hexdigest()
def copy(src,dst):
    regular(src);dst.mkdir(exist_ok=False)
    for p in sorted(src.iterdir()):
        regular(p)
        rel=p.relative_to(SOURCE).as_posix()
        if rel=="toolchain/lean-4.34.1-windows.zip":continue
        if p.is_dir():copy(p,dst/p.name)
        elif p.is_file():shutil.copy2(p,dst/p.name)
        else:raise RuntimeError(str(p))
regular(ROOT);regular(SOURCE)
cmd(["clone",str(SOURCE/"release/portable-release.bundle"),str(REPO)])
assert cmd(["rev-parse","HEAD"],REPO)=="0bdf00f9b75b43194436f9536b1bf09463fd5a5d"
cmd(["switch","-c","main"],REPO)
cmd(["remote","set-url","origin",REMOTE],REPO)
cmd(["config","user.name","OQ7 Release Assistant"],REPO)
cmd(["config","user.email","oq7-release@localhost"],REPO)
cmd(["config","core.autocrlf","false"],REPO)
cmd(["config","core.longpaths","true"],REPO)
copy(SOURCE,REPO/"review-package")
included=[]
for line in (SOURCE/"SHA256SUMS").read_text(encoding="utf-8").splitlines():
    expected,rel=line.split("  ",1)
    if rel=="toolchain/lean-4.34.1-windows.zip":continue
    assert sha(REPO/"review-package"/rel)==expected,rel
    included.append(rel)
before=cmd(["ls-tree","-r","--format=%(objectname) %(path)","HEAD","--","PrescribedExtinction","OQ7"],REPO)
main_readme=REPO/"README.md"
if main_readme.exists():shutil.copy2(main_readme,WORK/"ORIGINAL_REPOSITORY_README.md")
readme="""# OQ7 compact prescribed-extinction theorem

Private archival/review repository for the existing audited result. No new theorem or investigation is added by this upload.

The exact audited declaration is OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement at commit 686402a6c2d63820828729cc7ab02504632e3fe7. That original commit is preserved in the history and tagged audited-686402a. The separate portable packaging revision is tagged portable-0bdf00f. The 378 mathematical modules remain byte-identical.

## Review materials

- [Checked 16-page paper](review-package/manuscript/paper.pdf) and [manuscript source](review-package/manuscript/main.tex).
- [Complete deliverable index and S1–S4](review-package/RELEASE_INDEX.md).
- [Final package audit](review-package/FINAL_REVIEW_AUDIT.md), [claim-to-code correspondence](review-package/CLAIM_TO_CODE.md) and [audit provenance](review-package/AUDIT_PROVENANCE.md).
- [Reproduction commands](review-package/REPRODUCE.md), [exact regenerated commands](review-package/verification/COMMANDS.jsonl), [theorem type](review-package/FINAL_THEOREM_TYPE.txt), [axioms](review-package/FINAL_AXIOMS.txt), and [same-kernel fresh replay log](review-package/KERNEL_REPLAY.log).
- [All nine pinned dependency snapshots](review-package/release/dependency-sources/PINNED_DEPENDENCIES.json).
- [Historical version dispositions](review-package/VERSION_VERIFICATION_DISPOSITION.md) and [already-completed bounded priority comparison](review-package/priority/TARGETED_PRIORITY_REPORT.md).

The compiler archive is supplied inside the complete source-and-audit archive attached to the private release/draft on this repository's [Releases page](https://github.com/Dan-k391/oq7-prescribed-extinction/releases). It is too large for an ordinary Git blob. Extract that complete archive to obtain the exact sealed package, including the compiler. Its SHA-256 is recorded in GITHUB_UPLOAD.md. The package's SHA256SUMS covers the full package, so the compiler must be restored before checking every member against it.

## Claim scope

Gamma is the absolute absorption difference divided by the common dimensional extinction, equivalently the scattering difference divided by it. The same unchanged object/material law is used for opposite unit-amplitude waves with the same real y polarization. For fixed frequency and stated pointwise material caps, every strictly positive extinction target is exactly realized by a compact reciprocal local nonmagnetic anisotropic dielectric sequence. Radiation accounting includes the whole sphere and both polarizations. The unit supremum is strictly nonattained.

Dimensions are unrestricted across the sequence; there is no common positive loss floor, fixed-resource guarantee or bandwidth claim. The statement is not expanded to every interpretation of OQ7.

The recovered final-commit audit and regenerated strict checking support the final theorem's formal-verification claim. Only propext, Classical.choice and Quot.sound occur in the theorem dependency axioms. Fresh replay uses the same Lean kernel. AI-assisted semantic and ordinary mathematical review are distinguished from human peer review, and independently implemented kernel checking is not claimed. First priority remains unresolved.

Historical originals are retained without rewriting their prior status. The uncompiled scalar thickness checkpoint and unrecovered 43-theorem finite-port source are not used as substitutes. The manuscript remains anonymous; named author metadata has not been supplied. This private repository is not a public preprint or journal submission.
"""
main_readme.write_text(readme,encoding="utf-8")
archive=json.loads((SOURCE.parent/"OQ7-final-review-ARCHIVE_CHECK-0c32f324.json").read_text(encoding="utf-8"))
note="""# Private GitHub upload provenance

Destination: https://github.com/Dan-k391/oq7-prescribed-extinction (private).
Authorized by the user's 13 October 2026 request to create a private repository and upload the existing OQ7 repository. No other person is granted access.

This upload branches from the unchanged portable packaging commit 0bdf00f9b75b43194436f9536b1bf09463fd5a5d. The audited commit 686402a6c2d63820828729cc7ab02504632e3fe7 and all original parent history are preserved. Only a navigation README, this provenance note and the existing final review package are added. Git's upload-commit author is explicitly the release assistant; it is not manuscript-author metadata or a human review claim.

The complete archive (including the exact pinned compiler) is OQ7-final-review-complete-20261013-0c32f324.zip:
SHA-256 """+archive["complete"]["sha256"]+"""
Size: """+str(archive["complete"]["size_bytes"])+""" bytes.
Package SHA256SUMS file SHA-256: """+sha(SOURCE/"SHA256SUMS")+""".

The 850,624,573-byte toolchain/lean-4.34.1-windows.zip member is omitted from ordinary Git blobs and supplied inside that private attachment. Its SHA-256 is 457698d4e2132243e899ff32178d7ae63c16431d09ed9ad524d859c3581992af. All other 234 sealed manifest files are copied unchanged into review-package/. Cached build objects and local working checkouts are not uploaded.

The package's email status describes its sealing time. The prior email request remains unsent because sender-account selection is unresolved. Repository upload is separate from email or journal submission.
"""
(REPO/"GITHUB_UPLOAD.md").write_text(note,encoding="utf-8")
cmd(["add","--","README.md","GITHUB_UPLOAD.md","review-package"],REPO)
cmd(["commit","-m","Archive the completed OQ7 review package without changing the audited proof"],REPO)
after=cmd(["ls-tree","-r","--format=%(objectname) %(path)","HEAD","--","PrescribedExtinction","OQ7"],REPO)
assert before==after,"Mathematical source tree changed"
head=cmd(["rev-parse","HEAD"],REPO)
cmd(["tag","audited-686402a","686402a6c2d63820828729cc7ab02504632e3fe7"],REPO)
cmd(["tag","portable-0bdf00f","0bdf00f9b75b43194436f9536b1bf09463fd5a5d"],REPO)
tree=cmd(["ls-tree","-r","--format=%(objecttype) %(objectsize) %(path)","HEAD"],REPO)
for line in tree.splitlines():
    kind,size,path=line.split(" ",2)
    if kind=="blob" and int(size)>=100*1024*1024:raise RuntimeError("Oversize Git blob "+path)
status={"repository":REMOTE,"local_checkout":str(REPO),"upload_commit":head,"audited_commit":"686402a6c2d63820828729cc7ab02504632e3fe7","portable_commit":"0bdf00f9b75b43194436f9536b1bf09463fd5a5d","sealed_manifest_files_copied":len(included),"mathematical_source_tree_unchanged":True,"pinned_compiler":"private complete-archive attachment","sealed_archive":archive["complete"],"status":"prepared; not yet pushed"}
(WORK/"UPLOAD_PREPARED.json").write_text(json.dumps(status,indent=2)+"\n",encoding="utf-8")
print(json.dumps(status,indent=2))

