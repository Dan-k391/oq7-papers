from pathlib import Path
import hashlib
import json
import zipfile

root=Path(__file__).resolve().parents[1]
validation=json.loads((root/"review/validation.json").read_text(encoding="utf-8"))
if not validation["passed"]:
    raise RuntimeError("Release validation must pass before packaging")
names=["main.tex","references.bib","main.bbl","paper.pdf","paper.html","README.md",
       "build.py","template.html","theorem-correspondence.csv","theorem-correspondence.html",
       "outstanding-issues.txt","source-provenance.txt","reference-audit.txt","release-report.txt",
       "PUBLICATION_ISSUES.md","CHANGELOG.txt","MATHEMATICAL_CONSISTENCY.md",
       "figures/two-layer-geometry.pdf","figures/two-layer-geometry.svg",
       "build/main.aux","build/main.bbl","build/main.log","build/main.blg","build/tectonic-build.log",
       "build/format-correspondence.json","tools/tool-download-manifest.json"]
names += [p.relative_to(root).as_posix() for p in sorted((root/"reproducibility").glob("*")) if p.is_file()]
names += ["review/PublicationCheck.lean","review/CorrespondenceCheck.lean","review/publication-lean-check.log",
          "review/correspondence-lean-check.log","review/publication-fresh-kernel.log",
          "review/publication-source-check.json","review/lean-source-inventory.json","review/input-manifest.json",
          "review/validation.json","review/html-render-check.json","review/html-render-check.log",
          "review/check_html.cjs","review/validate_release.py","review/make_correspondence.py","review/package_release.py",
          "review/make_geometry.py","review/correction.diff",
          "review/pdf-contact-sheet.png","review/html-390-top.png","review/html-390-eq-amplitudes-minus.png",
          "review/html-1440-thm-main.png"]
names += [p.relative_to(root).as_posix() for p in sorted((root/"review").glob("corrected-page-*.png"))]
names += [p.relative_to(root).as_posix() for p in sorted((root/"review").glob("html-*.png"))]
names=sorted(set(names))
manifest=dict(release_date="2026-10-12",client_timezone="America/New_York",
              status="Focused corrections complete for professor review; final audit evidence unavailable; authorship/declarations/venue decisions pending",
              frozen_lean_commit=validation["frozen_commit"],
              authoritative_sources=["main.tex","references.bib"],
              files=[dict(path=n,bytes=(root/n).stat().st_size,sha256=hashlib.sha256((root/n).read_bytes()).hexdigest()) for n in names])
(root/"release-manifest.json").write_text(json.dumps(manifest,indent=2),encoding="utf-8")
names.append("release-manifest.json")
archive=root/"oq7-paper1-release.zip"
with zipfile.ZipFile(archive,"w",compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for n in names:z.write(root/n,"oq7-paper1-publication/"+n)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for entry in manifest["files"]:
        assert hashlib.sha256(z.read("oq7-paper1-publication/"+entry["path"])).hexdigest()==entry["sha256"]
arxiv=root/"oq7-paper1-arxiv-source.zip"
with zipfile.ZipFile(arxiv,"w",compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for n in ["main.tex","references.bib","main.bbl","figures/two-layer-geometry.pdf"]:z.write(root/n,n)
with zipfile.ZipFile(arxiv) as z:assert z.testzip() is None
info={p.name:dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in [archive,arxiv]}
(root/"archive-checksums.json").write_text(json.dumps(info,indent=2),encoding="utf-8")
print(json.dumps(dict(packaged_files=len(names),archives=info),indent=2))
