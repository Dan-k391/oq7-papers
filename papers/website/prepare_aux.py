"""Prepare isolated, exact-source TeX numbering for the HTML edition."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, uuid

SLUGS = ('prescribed-extinction', 'generalized-research', 'quartic-maxwell',
         'fixed-resource-bounds', 'compact-maxwell-cross-sections')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tectonic', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output', type=Path, required=True, help='New ignored scratch directory')
    args = parser.parse_args()
    root, out = args.root.resolve(), args.output.resolve()
    if out.exists():
        raise SystemExit('Use a fresh output directory; previous build evidence is preserved.')
    out.mkdir(parents=True)
    config = out / 'fonts.conf'
    config.write_text('<?xml version="1.0"?><fontconfig/>\n', encoding='utf-8')
    env = os.environ.copy()
    env.update(TECTONIC_CACHE_DIR=str(args.cache.resolve()), FONTCONFIG_FILE=str(config),
               SOURCE_DATE_EPOCH='1792065600')
    records = []
    for slug in SLUGS:
        source, work = root / 'papers' / slug / 'arxiv', out / slug
        (work / 'build').mkdir(parents=True)
        inputs = [source / name for name in ['main.tex', 'main.bbl', 'references.bib']]
        inputs += [p for p in (source / 'figures').rglob('*') if p.is_file()]
        before = {str(p.relative_to(source)): sha(p) for p in inputs}
        for path in inputs:
            target = work / path.relative_to(source)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
        command = [str(args.tectonic.resolve()), '--only-cached', '--untrusted', '--outfmt',
                   'xdv', '--keep-logs', '--keep-intermediates', '--outdir', 'build', 'main.tex']
        result = subprocess.run(command, cwd=work, env=env, capture_output=True, text=True,
                                encoding='utf-8', errors='replace')
        (work / 'console.log').write_text(result.stdout + result.stderr, encoding='utf-8')
        if result.returncode:
            raise SystemExit(f'TeX build failed: {slug}; inspect {work / "console.log"}')
        log = (work / 'build/main.log').read_text(encoding='utf-8', errors='replace')
        if re.search(r'undefined references|undefined citations|Rerun to get cross-references right', log, re.I):
            raise SystemExit('Unresolved TeX numbering: ' + slug)
        if before != {str(p.relative_to(source)): sha(p) for p in inputs}:
            raise SystemExit('Current source changed during build: ' + slug)
        if sha(work / 'build/main.bbl') != sha(source / 'main.bbl'):
            raise SystemExit('Regenerated bibliography differs: ' + slug)
        records.append({'slug': slug, 'inputs': before, 'aux_sha256': sha(work / 'build/main.aux'),
                        'bbl_sha256': sha(work / 'build/main.bbl'), 'exit_code': result.returncode})
        print(slug + ': auxiliary build passed')
    (out / 'build-record.json').write_text(json.dumps({'proof_code_executed': False,
        'current_sources_modified': False, 'papers': records}, indent=2) + '\n', encoding='utf-8')

if __name__ == '__main__':
    main()
