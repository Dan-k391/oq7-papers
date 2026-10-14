from pathlib import Path
import difflib,hashlib,json,shutil
OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324");WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\s0c32f324")
p=OUT/"manuscript/main.tex";s=p.read_text(encoding="utf-8")
s=s.replace(r"\paragraph{AI assistance and review status.}",r"\noindent\textbf{AI assistance and review status.}")
p.write_text(s,encoding="utf-8",newline="\n")
before=(OUT/"frozen/main.tex").read_text(encoding="utf-8")
(OUT/"MANUSCRIPT_EDITORIAL_CHANGES.diff").write_text("".join(difflib.unified_diff(before.splitlines(True),s.splitlines(True),fromfile="frozen/main.tex",tofile="manuscript/main.tex")),encoding="utf-8")
rec=json.loads((OUT/"MANUSCRIPT_PRESERVATION.json").read_text(encoding="utf-8"));rec["review_tex_sha256"]=hashlib.sha256(s.encode()).hexdigest()
(OUT/"MANUSCRIPT_PRESERVATION.json").write_text(json.dumps(rec,indent=2),encoding="utf-8")
dest=OUT/"verification/manuscript-build-attempt-1";dest.mkdir()
for name in ["MANUSCRIPT_BUILD.log","MANUSCRIPT_BUILD_COMMAND.json"]:
    shutil.copy2(OUT/"verification"/name,dest/name)
shutil.copy2(OUT/"manuscript/build/tectonic-build.log",dest/"tectonic-build.log")
runner=WORK/"build_review_pdf.py";code=runner.read_text(encoding="utf-8").replace('shutil.copytree(ROOT/"outputs/oq7-paper1-publication/tools/tectonic-cache",cache)','if not cache.exists():shutil.copytree(ROOT/"outputs/oq7-paper1-publication/tools/tectonic-cache",cache)')
runner.write_text(code,encoding="utf-8")

