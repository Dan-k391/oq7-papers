from pathlib import Path
import concurrent.futures, hashlib, json, urllib.request, zipfile
from pypdf import PdfReader
ROOT=Path(__file__).parent
SOURCES=[
("bruno2016_published","https://authors.library.caltech.edu/records/w3sjb-41r38/files/15m1033782.pdf?download=1",".pdf"),
("bruno2016_supp","https://epubs.siam.org/doi/suppl/10.1137/15M1033782/suppl_file/wgf_method_supp_mats.zip",".zip")]
def get(item):
    key,url,ext=item
    r={"id":key,"url":url}
    try:
        with urllib.request.urlopen(url,timeout=35) as resp:data=resp.read()
        p=ROOT/(key+ext);p.write_bytes(data)
        r.update(status="recovered",sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
        if ext==".pdf":
            reader=PdfReader(p);r["pages"]=len(reader.pages)
            (ROOT/(key+".txt")).write_text("\n\n".join("=== PDF PAGE "+str(i+1)+" ===\n"+(page.extract_text() or "") for i,page in enumerate(reader.pages)),encoding="utf-8")
        else:
            with zipfile.ZipFile(p) as z:r["entries"]=z.namelist()
    except Exception as exc:r.update(status="unrecovered",error=str(exc))
    return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:result=list(ex.map(get,SOURCES))
(ROOT/"retrieval_final.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
print(json.dumps(result,indent=2))

