import hashlib
import importlib.util
import json
import shutil
from pathlib import Path

from pypdf import PdfReader

root = Path(__file__).resolve().parents[1] / 'outputs' / 'oq7-mission'
refs = root / 'references'
out = root / 'extracted'
refs.mkdir(parents=True, exist_ok=True)
out.mkdir(parents=True, exist_ok=True)
papers = {
    'PaperA': Path(r'C:\Users\Daniel\Downloads\OQ7_generalized_research_2026-10-10.pdf'),
    'PaperB': Path(r'C:\Users\Daniel\Downloads\OQ7_compact_Maxwell_cross_sections_2026-10-10.pdf'),
    'Tutorial': Path(r'C:\Users\Daniel\Downloads\2605.24738v1.pdf'),
}
manifest = []
for key, source in papers.items():
    target = refs / source.name
    if not target.exists():
        shutil.copyfile(source, target)
    before = hashlib.sha256(source.read_bytes()).hexdigest()
    copied = hashlib.sha256(target.read_bytes()).hexdigest()
    if before != copied:
        raise RuntimeError(f'Copy mismatch: {source}')
    reader = PdfReader(str(target))
    pages = [{'page': i + 1, 'text': p.extract_text() or ''} for i, p in enumerate(reader.pages)]
    (out / f'{key}.json').write_text(json.dumps(pages, ensure_ascii=False, indent=2), encoding='utf-8')
    (out / f'{key}.txt').write_text('\n\n'.join(f'===== PDF PAGE {p["page"]} =====\n{p["text"]}' for p in pages), encoding='utf-8')
    manifest.append({'id': key, 'original': str(source), 'copy': str(target), 'pages': len(pages), 'sha256': before, 'metadata': str(reader.metadata), 'first_page': pages[0]['text'][:1100]})
(root / 'reference_manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding='utf-8')
print(json.dumps(manifest, ensure_ascii=False, indent=2))
