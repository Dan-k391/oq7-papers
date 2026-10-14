from pathlib import Path
import datetime, json, os, shutil, subprocess
from pypdf import PdfReader
import pypdfium2 as pdfium
from PIL import Image,ImageDraw
ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1");OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324");WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\s0c32f324")
draft=OUT/"manuscript";logdir=OUT/"verification"
cache=WORK/"tectonic-cache"
if not cache.exists():shutil.copytree(ROOT/"outputs/oq7-paper1-publication/tools/tectonic-cache",cache)
env=dict(os.environ);env.update(TECTONIC_CACHE_DIR=str(cache),PYTHONUTF8="1")
python=Path(r"C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
tools=ROOT/"outputs/oq7-paper1-publication/tools"
argv=[str(python),str(draft/"build.py"),"--tectonic",str(tools/"tectonic/tectonic.exe"),"--pandoc",str(tools/"pandoc/pandoc-3.12.1/pandoc.exe")]
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (logdir/"MANUSCRIPT_BUILD.log").open("wb") as f:r=subprocess.run(argv,cwd=draft,env=env,stdout=f,stderr=subprocess.STDOUT)
rec=dict(argv=argv,cwd=str(draft),environment=dict(TECTONIC_CACHE_DIR=str(cache)),started_utc=started,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=r.returncode)
(logdir/"MANUSCRIPT_BUILD_COMMAND.json").write_text(json.dumps(rec,indent=2),encoding="utf-8")
if r.returncode:raise RuntimeError("Manuscript build failed; see full log")
for name in ["tectonic-build.log","format-correspondence.json"]:shutil.copy2(draft/"build"/name,logdir/name)
pdf=PdfReader(draft/"paper.pdf")
(logdir/"PDF_TEXT.txt").write_text("\n\n".join("=== PAGE "+str(i+1)+" ===\n"+(p.extract_text() or "") for i,p in enumerate(pdf.pages)),encoding="utf-8")
qa=WORK/"pdf-qa";qa.mkdir()
doc=pdfium.PdfDocument(draft/"paper.pdf");tiles=[]
for i,page in enumerate(doc):
    im=page.render(scale=1.6).to_pil().convert("RGB")
    im.save(qa/f"page-{i+1:02d}.png")
    im.thumbnail((350,465));tile=Image.new("RGB",(370,495),"#eeeeee");tile.paste(im,((370-im.width)//2,8))
    ImageDraw.Draw(tile).text((8,478),f"Page {i+1}",fill="black");tiles.append(tile)
for group in range(0,len(tiles),8):
    subset=tiles[group:group+8]
    sheet=Image.new("RGB",(1480,990),"white")
    for j,tile in enumerate(subset):sheet.paste(tile,((j%4)*370,(j//4)*495))
    sheet.save(qa/f"sheet-{group//8+1}.png")
print("PDF_PAGES",len(pdf.pages))
print((logdir/"MANUSCRIPT_BUILD.log").read_text(encoding="utf-8"))

