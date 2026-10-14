import datetime,json,os,pathlib,shutil,subprocess,sys
root=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1'); work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\r59a36c60'); out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-release-20261013-final-audit-59a36c60')
draft=work/'manuscript'; shutil.copytree(out/'manuscript',draft,dirs_exist_ok=True)
pub=root/'outputs/oq7-paper1-publication'
cache=work/'cache/tectonic'; shutil.copytree(pub/'tools/tectonic-cache',cache,dirs_exist_ok=True)
env=dict(os.environ); env.update(TECTONIC_CACHE_DIR=str(cache),PYTHONUTF8='1')
args=[sys.executable,str(draft/'build.py'),'--tectonic',str(pub/'tools/tectonic/tectonic.exe'),'--pandoc',str(pub/'tools/pandoc/pandoc-3.12.1/pandoc.exe')]
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (out/'portable-test-logs/manuscript-build.log').open('wb') as f: r=subprocess.run(args,cwd=draft,env=env,stdout=f,stderr=subprocess.STDOUT)
record={'argv':args,'cwd':str(draft),'environment':{'TECTONIC_CACHE_DIR':str(cache)},'started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':r.returncode}
(out/'portable-test-logs/MANUSCRIPT_BUILD_COMMAND.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
if r.returncode: raise RuntimeError('Manuscript compile failed; see log')
for name in ['paper.pdf','paper.html','main.bbl']: shutil.copyfile(draft/name,out/'manuscript'/name)
for name in ['tectonic-build.log','format-correspondence.json']: shutil.copyfile(draft/'build'/name,out/'portable-test-logs'/name)
from pypdf import PdfReader
p=PdfReader(out/'manuscript/paper.pdf'); print('UPDATED_PDF_PAGES='+str(len(p.pages)))
print((out/'portable-test-logs/manuscript-build.log').read_text(encoding='utf-8'))
# Render every page for visual QA; images are scratch artifacts.
import pypdfium2 as pdfium
document=pdfium.PdfDocument(out/'manuscript/paper.pdf'); render=work/'pdf-qa'; render.mkdir(exist_ok=True)
from PIL import Image, ImageOps, ImageDraw
tiles=[]
for i,page in enumerate(document):
 page.render(scale=1.5).to_pil().save(render/('page-%02d.png'%(i+1)))
 im=Image.open(render/('page-%02d.png'%(i+1))).convert('RGB'); im.thumbnail((300,410))
 tile=Image.new('RGB',(320,440),'#dddddd'); tile.paste(im,((320-im.width)//2,20)); ImageDraw.Draw(tile).text((8,420),'Page '+str(i+1),fill='black'); tiles.append(tile)
sheet=Image.new('RGB',(1280,440*((len(tiles)+3)//4)),'white')
for i,im in enumerate(tiles): sheet.paste(im,((i%4)*320,(i//4)*440))
sheet.save(render/'contact-sheet.png')
print('RENDERED_ALL_PAGES')
