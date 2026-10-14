from pathlib import Path
import concurrent.futures, hashlib, json, urllib.request
from pypdf import PdfReader
ROOT=Path(__file__).parent
SOURCES=[
("armitage2014","https://arxiv.org/pdf/1311.5556"),
("sounas2017","https://link.aps.org/accepted/10.1103/PhysRevLett.118.154302"),
("andersen2005","https://vbn.aau.dk/ws/files/19704710/Absorption_Efficiency.pdf"),
("bruno2016","https://arxiv.org/pdf/1507.04445"),
("arrieta2022","https://arxiv.org/pdf/2210.02565"),
("khurgin2021","https://uriellevy.huji.ac.il/sites/default/files/uriellevy/files/emulating_exceptional-point_encirclements_using_imperfect_eaky_photonic_components_asymmetric_mode-switching_and_omni-polarizer_action.pdf"),
("gustafsson2012","https://lup.lub.lu.se/search/files/96358663/TEAT_7213.pdf"),
("radi2013","https://arxiv.org/pdf/1211.3549"),
("kononchuk2019","https://arxiv.org/pdf/1903.01507"),
("mann2023_booklet","https://congress2023.metamorphose-vi.org/files/METAMATERIALS_2023_BOOKLET.pdf"),
("sounas2014","https://opg.optica.org/viewmedia.cfm?uri=ol-39-13-4053&seq=0"),
("manez2026","https://onlinelibrary.wiley.com/doi/pdf/10.1002/nap2.70145"),
("hopkins2015","https://www.mdpi.com/2304-6732/2/2/745/pdf")]
def get(item):
    key,url=item
    r={"id":key,"url":url}
    try:
        req=urllib.request.Request(url,headers={"User-Agent":"OQ7-priority-research/1.0"})
        with urllib.request.urlopen(req,timeout=35) as resp:
            data=resp.read()
            r["resolved_url"]=resp.geturl()
            r["content_type"]=resp.headers.get("Content-Type")
        if not data.startswith(b"%PDF"):
            r["status"]="not PDF";r["bytes"]=len(data)
            return r
        target=ROOT/(key+".pdf"); target.write_bytes(data)
        reader=PdfReader(target)
        r.update(status="full PDF recovered",sha256=hashlib.sha256(data).hexdigest(),pages=len(reader.pages),bytes=len(data))
        text="\n\n".join("=== PDF PAGE "+str(i+1)+" ===\n"+(page.extract_text() or "") for i,page in enumerate(reader.pages))
        (ROOT/(key+".txt")).write_text(text,encoding="utf-8")
    except Exception as exc:
        r["status"]="unrecovered";r["error"]=str(exc)
    return r
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
    result=list(ex.map(get,SOURCES))
(ROOT/"retrieval.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
for r in result:
    print(r["id"],r["status"],r.get("pages",""),r.get("sha256",""),r.get("error",""))

