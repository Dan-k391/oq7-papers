"""Build and package one current manuscript from a fresh, source-only directory.

Uses local TeX executables, without shell escape. Does not execute proof code.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PAPERS = ('prescribed-extinction', 'quartic-maxwell', 'generalized-research',
          'fixed-resource-bounds', 'compact-maxwell-cross-sections')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, cwd, label):
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                            encoding='utf-8', errors='replace')
    (cwd / (label + '-console.txt')).write_text(result.stdout + result.stderr,
                                              encoding='utf-8')
    if result.returncode:
        raise SystemExit(f'{label} failed; inspect {cwd / (label + "-console.txt")}')


def build(paper, tex_dir=None):
    source = ROOT / 'papers' / paper / 'arxiv'
    tex = (source / 'main.tex').read_text(encoding='utf-8')
    if r'\today' in tex or r'\write18' in tex:
        raise SystemExit('Variable date or shell invocation in manuscript')
    for email in ('denialk391@gmail.com', 'zjj2785@gmail.com'):
        if email not in tex:
            raise SystemExit('Missing enduring author email: ' + email)
        if r'\href{mailto:' + email + r'}{\texttt{' + email + '}}' not in tex:
            raise SystemExit('Missing standardized clickable contact: ' + email)
    if tex.index('Daniel Wang') > tex.index('Junjie Zheng'):
        raise SystemExit('Incorrect author order')

    # Only compilation inputs and explicitly supplied ancillary files enter upload.
    inputs = [source / 'main.tex']
    if r'\bibliography{' in tex:
        inputs.append(source / 'references.bib')
    for name in re.findall(r'\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}', tex):
        path = source / name
        if not path.is_file() or path.resolve().is_relative_to(source.resolve()) is False:
            raise SystemExit('Missing or external figure: ' + name)
        inputs.append(path)
    anc = source / 'anc'
    if anc.exists():
        inputs.extend(sorted(p for p in anc.rglob('*') if p.is_file()))
    inputs = sorted(set(inputs), key=lambda p: p.relative_to(source).as_posix())
    for path in inputs:
        relative = path.relative_to(source)
        if any(not re.fullmatch(r'[A-Za-z0-9_+.,=\-]+', part) or part.startswith('.')
               for part in relative.parts):
            raise SystemExit('Unsuitable upload name: ' + str(relative))
        if relative.parts[0] == 'anc' and path.suffix.lower() == '.tex':
            raise SystemExit('TeX must not be placed in anc/')

    # A unique directory avoids stale auxiliaries; ordinary inherited Windows ACLs
    # also allow the desktop sandbox to write its child directories.
    import uuid
    work_root = ROOT / '.local' / 'arxiv-build'
    work_root.mkdir(parents=True, exist_ok=True)
    work = work_root / (paper + '-' + uuid.uuid4().hex[:12])
    work.mkdir()
    for path in inputs:
        destination = work / path.relative_to(source)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
    engine_name = 'pdflatex'
    engine = str(Path(tex_dir) / (engine_name + '.exe')) if tex_dir else engine_name
    bibtex = str(Path(tex_dir) / 'bibtex.exe') if tex_dir else 'bibtex'
    command = [engine, '-no-shell-escape', '-halt-on-error',
               '-interaction=nonstopmode', '-file-line-error', 'main.tex']
    run(command, work, 'tex-pass1')
    if r'\bibliography{' in tex:
        run([bibtex, 'main'], work, 'bibtex')
    run(command, work, 'tex-pass2')
    run(command, work, 'tex-pass3')
    log = (work / 'main.log').read_text(encoding='utf-8', errors='replace')
    tex_passes = 3
    while 'Rerun to get cross-references right' in log and tex_passes < 6:
        tex_passes += 1
        run(command, work, 'tex-pass' + str(tex_passes))
        log = (work / 'main.log').read_text(encoding='utf-8', errors='replace')
    failures = ('undefined references', 'undefined citations', 'Citation ',
                'Reference ', 'Rerun to get cross-references right')
    if any(s in log for s in failures):
        raise SystemExit('Unresolved reference or citation; inspect ' + str(work / 'main.log'))
    overfull = re.findall(r'Overfull \\[hv]box[^\n]*', log)
    shutil.copyfile(work / 'main.pdf', source / 'paper.pdf')
    if (work / 'main.bbl').exists():
        shutil.copyfile(work / 'main.bbl', source / 'main.bbl')
        inputs.append(source / 'main.bbl')
    entries = []
    archive = source / 'arxiv-source.zip'
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED) as z:
        for path in sorted(inputs, key=lambda p: p.relative_to(source).as_posix()):
            name = path.relative_to(source).as_posix()
            item = zipfile.ZipInfo(name, date_time=(2026, 10, 14, 0, 0, 0))
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = 0o100644 << 16
            z.writestr(item, path.read_bytes())
            entries.append(dict(path=name, sha256=sha(path), bytes=path.stat().st_size))
    from pypdf import PdfReader
    reader = PdfReader(source / 'paper.pdf')
    result = dict(paper=paper, engine='pdfLaTeX', local_texlive='2024',
                  shell_escape=False, fresh_directory=True, tex_passes=tex_passes,
                  pages=len(reader.pages),
                  pdf_sha256=sha(source / 'paper.pdf'), zip_sha256=sha(archive),
                  inputs=entries, unresolved_references=False, overfull_boxes=overfull,
                  arxiv_server_tested=False, proof_code_executed=False)
    (source / 'BUILD_VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: result[k] for k in ('paper', 'pages', 'overfull_boxes', 'pdf_sha256')}))
    print('Logs:', work)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paper', choices=PAPERS)
    parser.add_argument('--tex-dir', help='Directory containing pdflatex.exe and bibtex.exe')
    args = parser.parse_args()
    build(args.paper, args.tex_dir)
