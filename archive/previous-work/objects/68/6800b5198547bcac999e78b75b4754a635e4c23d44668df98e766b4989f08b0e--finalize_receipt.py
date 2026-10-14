from pathlib import Path
import datetime,hashlib,json,shutil,os,stat
ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1")
OUT=ROOT/"outputs/OQ7-GitHub-upload-20261013-0c32f324"
WORK=ROOT/"work/github-upload-20261013-0c32f324"
SEALED=ROOT/"outputs/OQ7-final-review-20261013-0c32f324"
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
    return h.hexdigest()
def regular(p):
    st=os.lstat(p)
    assert not(getattr(st,"st_file_attributes",0)&0x400 or stat.S_ISLNK(st.st_mode)),str(p)
regular(OUT)
browser=json.loads((OUT/"BROWSER_CONFIRMATION.json").read_text())
prep=json.loads((WORK/"UPLOAD_GIT_BLOBS_VERIFIED.json").read_text())
assert browser["uploaded_archive_sha256_from_GitHub"]==prep["sealed_archive"]["sha256"]
assert browser["uploaded_checksum_sidecar_sha256_from_GitHub"]==sha(SEALED.parent/"OQ7-final-review-complete-20261013-0c32f324.zip.sha256")
refs=(WORK/"REMOTE_REFS.log").read_text(encoding="utf-8-sig")
for commit,ref in [(prep["upload_commit"],"refs/heads/main"),(prep["audited_commit"],"refs/tags/audited-686402a"),(prep["portable_commit"],"refs/tags/portable-0bdf00f")]:
    assert commit+"\t"+ref in refs
# Recheck sealed local files without rewriting the original package.
for line in (SEALED/"SHA256SUMS").read_text().splitlines():
    h,rel=line.split("  ",1)
    regular(SEALED/rel);assert sha(SEALED/rel)==h,rel
assert sha(SEALED/"SHA256SUMS")=="7461247fcede183e04104e83c77acc5062f063884fa74ad5041299a54fe95af9"
for name in ["PUSH.log","PUSH_REVIEW_TAG.log","REMOTE_REFS.log","LOCAL_COMMANDS.jsonl","UPLOAD_PREPARED.json","UPLOAD_GIT_BLOBS_VERIFIED.json"]:
    shutil.copy2(WORK/name,OUT/name)
status={
"status":"COMPLETE",
"user_facing_date":"13 October 2026, America/New_York",
"recorded_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
"repository":browser["repository"],"visibility":"private; verified in GitHub UI",
"uploaded_review_commit":prep["upload_commit"],
"audited_commit":prep["audited_commit"],"audited_tag":"audited-686402a",
"portable_commit":prep["portable_commit"],"portable_tag":"portable-0bdf00f",
"review_tag":"review-package-2026-10-13",
"source_history":"preserved; 63 commits visible in GitHub UI",
"mathematical_source_tree_unchanged":True,
"all_234_uploaded_package_git_blob_sha256_match":True,
"all_235_sealed_local_package_files_unchanged_after_upload":True,
"complete_archive_attachment":{
"draft_url":browser["draft"],"status":"saved private draft",
"name":browser["asset_names"][0],"size_bytes":958191948,
"sha256_local_and_GitHub":browser["uploaded_archive_sha256_from_GitHub"],
"checksum_sidecar_sha256_local_and_GitHub":browser["uploaded_checksum_sidecar_sha256_from_GitHub"],
"compiler_included":True,"all_nine_pinned_dependency_snapshots_included":True,
"transfer_verification":"GitHub's displayed server digest matches the local archive SHA-256; no redundant 958 MB download needed"
},
"browser_file_access":{
"initial_setting":"disabled; upload tool rejected access",
"temporary_enablement":"user approved; browser security rejected opening edge://extensions; user manually enabled and confirmed",
"restoration":"user explicitly confirmed Disabled again after upload",
"settings_independently_inspected":False
},
"publication_preprint_journal_submission":"not performed",
"email":"not sent; prior Gmail sender choice unresolved",
"original_working_trees_and_synced_sources":"preserved"
}
(OUT/"GITHUB_UPLOAD_RECEIPT.json").write_text(json.dumps(status,indent=2)+"\n",encoding="utf-8")
readme="""# Private OQ7 repository upload receipt

Repository: [Dan-k391/oq7-prescribed-extinction](https://github.com/Dan-k391/oq7-prescribed-extinction), verified **Private** in the logged-in browser.

The complete preserved source history is uploaded. The exact audited commit is 686402a6c2d63820828729cc7ab02504632e3fe7 (tag audited-686402a), and the portable revision is 0bdf00f9b75b43194436f9536b1bf09463fd5a5d (tag portable-0bdf00f). The new archive/navigation-only upload commit is fbbfc9415f0531ed6981e9281d5059f98c7e39cc (tag review-package-2026-10-13). The 378 mathematical modules are unchanged. GitHub displays 63 commits.

The paper, manuscript source, S1–S4, nine pinned dependency snapshots, original audit evidence, regenerated logs, correspondence and existing priority reports are present in review-package/. All 234 copied sealed-package Git blobs match their SHA-256 identities.

The compiler is included in the 958,191,948-byte complete source-and-audit archive attached to the [saved private draft](https://github.com/Dan-k391/oq7-prescribed-extinction/releases/tag/untagged-b5b28cdc77149a3e210e). GitHub's server digest matches the local archive:
a3b0b8c10977912634937bcac421908c83d959555bbe35858cb4124d682f9510.
The checksum sidecar is also uploaded and its server digest matches. This is an unpublished private draft, not a public preprint or journal submission.

The original sealed local package and its 235 manifest files were rechecked after upload and remain unchanged. The new GitHub receipt is separate from that package.

Local-file browser access was temporarily enabled manually by the user after explicit approval. The user confirmed that it was disabled again after upload. The browser security policy blocked direct inspection/control of edge://extensions; this receipt does not fabricate independent inspection of the setting.

No email was sent. The prior Gmail sender-account choice remains unresolved. No new research, proof work, peer-review certification or novelty claim was added.

The screenshots show the actual private repository and saved draft/asset state. Command and identity records accompany this receipt.
"""
(OUT/"README.md").write_text(readme,encoding="utf-8")
files=sorted(p for p in OUT.iterdir() if p.is_file() and p.name!="SHA256SUMS")
for p in files:regular(p)
(OUT/"SHA256SUMS").write_text("".join(sha(p)+"  "+p.name+"\n" for p in files),encoding="utf-8")
print(json.dumps({"status":"COMPLETE","repository":browser["repository"],"private_draft":browser["draft"],"file_access_restore":"user-confirmed disabled","receipt_directory":str(OUT),"receipt_files":len(files)+1},indent=2))

