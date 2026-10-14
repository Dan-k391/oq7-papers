from pathlib import Path
import concurrent.futures, hashlib, json, urllib.request
from pypdf import PdfReader
ROOT=Path(__file__).parent
SOURCES=[
("khurgin2021_author","https://uriellevy.huji.ac.il/sites/default/files/uriellevy/files/emulating_exceptional-point_encirclements_using_imperfect_eaky_photonic_components_asymmetric_mode-switching_and_omni-polarizer_action.pdf"),
("khurgin2021_preprint","https://arxiv.org/pdf/2009.04038"),
("hopkins2015_cdn","https://mdpi-res.com/d_attachment/photonics/photonics-02-00745/article_deploy/photonics-02-00745.pdf"),
("schab2020","https://arxiv.org/pdf/2009.08502"),
("manez2026_html","https://onlinelibrary.wiley.com/doi/full/10.1002/nap2.70145")]
def get(item):
    key,url=item
    rec={"id":key,"url":url}
    try:
        req=urllib.request.Request(url,headers={"User-Agent":"OQ7-priority-research/1.0"})
        with urllib.request.urlopen(req,timeout=35) as resp:
            rec.update(http_status=resp.status,resolved_url=resp.geturl(),content_type=resp.headers.get("Content-Type"))
            data=resp.read()
        if not data.startswith(b"%PDF"):
            rec["status"]="HTML retrieved"; ext=".html"
        else:rec["status"]="full PDF recovered";ext=".pdf"
        (ROOT/(key+ext)).write_bytes(data)
        rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
        if ext==".pdf":
            reader=PdfReader(ROOT/(key+ext)); rec["pages"]=len(reader.pages)
            (ROOT/(key+".txt")).write_text("\n\n".join("=== PDF PAGE "+str(i+1)+" ===\n"+(page.extract_text() or "") for i,page in enumerate(reader.pages)),encoding="utf-8")
    except Exception as exc: rec.update(status="unrecovered",error=str(exc))
    return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:result=list(ex.map(get,SOURCES))
(ROOT/"retrieval_second.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
for rec in result:print(rec)

