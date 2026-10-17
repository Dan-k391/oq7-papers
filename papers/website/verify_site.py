"""Independently check the five-paper static release without running proofs.

The checker reads the current manuscript inputs, fresh exact-source TeX AUX/BBL,
and generated HTML. It does not import the site builder or trust its inventories
in place of recomputing them. Reports describe publication-format consistency,
not mathematical validity, novelty, peer review, or a deployment result.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit
import xml.etree.ElementTree as ET
import zipfile

PAPERS = ('prescribed-extinction', 'generalized-research', 'quartic-maxwell',
          'fixed-resource-bounds', 'compact-maxwell-cross-sections')
THEOREMS = {'theorem', 'lemma', 'proposition', 'corollary', 'remark'}
VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link',
        'meta', 'param', 'source', 'track', 'wbr'}
TRACKERS = re.compile(r'google-analytics|googletagmanager|doubleclick|hotjar|'
                      r'clarity\.ms|plausible\.io|segment\.com|facebook\.net', re.I)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized(text):
    return ' '.join(text.split())


class Node:
    def __init__(self, tag, attrs=(), parent=None):
        self.tag, self.attrs, self.parent = tag, dict(attrs), parent
        self.children = []

    def text(self, omit_annotation=True):
        if omit_annotation and self.tag in {'annotation', 'script', 'style'}:
            return ''
        return ''.join(c if isinstance(c, str) else c.text(omit_annotation)
                       for c in self.children)

    def descendants(self, tag=None):
        for child in self.children:
            if isinstance(child, Node):
                if tag is None or child.tag == tag:
                    yield child
                yield from child.descendants(tag)

    def classes(self):
        return set(self.attrs.get('class', '').split())


class Page(HTMLParser):
    def __init__(self, path):
        super().__init__(convert_charrefs=True)
        self.path, self.root = path, Node('document')
        self.stack, self.ids, self.duplicates, self.links = [self.root], {}, [], []
        self.raw = path.read_text(encoding='utf-8')
        self.feed(self.raw)
        self.close()

    def add(self, tag, attrs, closed=False):
        node = Node(tag.lower(), attrs, self.stack[-1])
        self.stack[-1].children.append(node)
        ident = node.attrs.get('id')
        if ident:
            if ident in self.ids:
                self.duplicates.append(ident)
            self.ids[ident] = node
        for attr in ('href', 'src', 'poster'):
            if attr in node.attrs:
                self.links.append((node, attr, node.attrs[attr]))
        if not closed and node.tag not in VOID:
            self.stack.append(node)

    def handle_starttag(self, tag, attrs):
        self.add(tag, attrs)

    def handle_startendtag(self, tag, attrs):
        self.add(tag, attrs, True)

    def handle_endtag(self, tag):
        for i in range(len(self.stack)-1, 0, -1):
            if self.stack[i].tag == tag.lower():
                del self.stack[i:]
                return

    def handle_data(self, text):
        self.stack[-1].children.append(text)


def read_group(text, pos):
    """Read a balanced TeX group without relying on a flat-brace regexp."""
    while pos < len(text) and text[pos].isspace():
        pos += 1
    if pos >= len(text) or text[pos] != '{':
        raise ValueError('Expected TeX group near ' + text[pos:pos+60])
    depth, start, pos = 1, pos+1, pos+1
    while pos < len(text):
        if text[pos] == '\\':
            pos += 2
            continue
        if text[pos] == '{':
            depth += 1
        elif text[pos] == '}':
            depth -= 1
            if depth == 0:
                return text[start:pos], pos+1
        pos += 1
    raise ValueError('Unclosed TeX group')


def aux_inventory(text):
    labels = {}
    for match in re.finditer(r'\\newlabel\s*(?=\{)', text):
        key, pos = read_group(text, match.end())
        value, _ = read_group(text, pos)
        number, _ = read_group(value, 0)
        if key in labels:
            raise ValueError('Duplicate AUX label: ' + key)
        labels[key] = number
    headings = re.findall(r'\\contentsline\s*\{(section|subsection|subsubsection)\}'
                          r'\s*\{\\numberline\s*\{([^}]+)\}', text)
    citations = {}
    for match in re.finditer(r'\\bibcite\s*(?=\{)', text):
        key, pos = read_group(text, match.end())
        value, _ = read_group(text, pos)
        number, _ = read_group(value, 0)
        citations[key] = number
    return labels, headings, citations


def source_inventory(text):
    # Current manuscripts have no verbatim/code environments containing commands.
    text = re.sub(r'(?<!\\)%[^\n]*', '', text)
    equations = re.findall(r'\\label\{(eq:[^}]+)\}', text)
    figures = re.findall(r'\\label\{(fig:[^}]+)\}', text)
    theorem_rows = []
    for match in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary|remark)\}'
                             r'(?:\[[^]]*\])?(.*?)\\end\{\1\}', text, re.S):
        labels = re.findall(r'\\label\{([^}]+)\}', match[2])
        theorem_rows.append((match[1], labels[0] if labels else None))
    citations = {key.strip() for match in re.finditer(r'\\citep(?:\[[^]]*\])*\{([^}]+)\}', text)
                 for key in match[1].split(',')}
    return equations, figures, theorem_rows, citations


def run(args):
    root, site, auxroot = args.root.resolve(), args.site.resolve(), args.aux_root.resolve()
    errors, warnings, records = [], [], []

    def check(ok, message):
        if not ok:
            errors.append(message)
        return ok

    pages = {p.resolve(): Page(p.resolve()) for p in sorted(site.rglob('*.html'))}
    check((site/'index.html') in pages, 'Missing directory index.html')
    check(len(pages) >= 6, 'Fewer than the directory plus five complete HTML papers')

    def local_target(page, url):
        parsed = urlsplit(url)
        if parsed.scheme or parsed.netloc:
            return None, parsed.fragment
        path = unquote(parsed.path)
        if path.startswith('/'):
            base = '/' + args.base_path.strip('/') if args.base_path.strip('/') else ''
            if base and (path == base or path.startswith(base+'/')):
                path = path[len(base):]
            target = site/path.lstrip('/')
        else:
            target = page.path.parent/path if path else page.path
        if target.is_dir() or path.endswith('/'):
            target = target/'index.html'
        return target.resolve(), unquote(parsed.fragment)

    local_links = 0
    for page in pages.values():
        relative = page.path.relative_to(site).as_posix()
        check(not page.duplicates, relative+': duplicate IDs: '+str(page.duplicates))
        text = page.root.text()
        check('??' not in text, relative+': unresolved literal ??')
        check('\ufffd' not in page.raw, relative+': replacement/missing character')
        check(not re.search(r'\[(?:@|\?|citation needed)|CITATION NOT FOUND|'
                            r'undefined reference|unresolved reference', text, re.I),
              relative+': unresolved reference/citation marker')
        check(not re.search(r'\\(?:citep|eqref|ref)\{', text),
              relative+': raw unconverted citation/reference command')
        for script in page.root.descendants('script'):
            check(not script.attrs.get('src'), relative+': script src is unnecessary for native MathML')
            check(not re.search(r'https?://|sendBeacon|XMLHttpRequest|WebSocket|'
                                r'\bfetch\s*\(|\bgtag\s*\(', script.text(False), re.I),
                  relative+': inline script contains network/tracking behavior')
        for node, attr, url in page.links:
            parsed = urlsplit(url)
            check(not TRACKERS.search(url), relative+': tracking URL: '+url)
            check(parsed.scheme.lower() not in {'javascript', 'vbscript', 'file'},
                  relative+': unsafe URL scheme: '+url)
            external = bool(parsed.scheme or parsed.netloc)
            if external:
                resource = attr != 'href' or node.tag in {'link', 'script'}
                check(not resource or parsed.scheme == 'data',
                      relative+': remote runtime resource: '+url)
                continue
            target, fragment = local_target(page, url)
            local_links += 1
            if not check(target.is_relative_to(site), relative+': local link escapes site: '+url):
                continue
            if not check(target.is_file(), relative+': missing local target: '+url):
                continue
            if fragment and target.suffix.lower() in {'.html', '.htm'}:
                check(target in pages and fragment in pages[target].ids,
                      relative+': missing fragment target: '+url)
            elif fragment and target.suffix.lower() == '.svg':
                ids = {el.get('id') for el in ET.parse(target).iter() if el.get('id')}
                check(fragment in ids, relative+': missing SVG fragment: '+url)
        for node in page.root.descendants('span'):
            if 'math' in node.classes():
                check(any(node.descendants('math')), relative+': math fallback without native MathML')
    for path in site.rglob('*.css'):
        css = path.read_text(encoding='utf-8')
        check(not re.search(r'@import|url\(\s*[\'"]?(?:https?:)?//', css, re.I),
              path.relative_to(site).as_posix()+': remote CSS/font resource')

    landing = pages.get(site/'index.html')
    landing_targets = {local_target(landing, url)[0] for _, attr, url in landing.links
                       if attr == 'href' and not (urlsplit(url).scheme or urlsplit(url).netloc)} if landing else set()
    for slug in PAPERS:
        source, target = root/'papers'/slug/'arxiv', site/slug
        page = pages.get(target/'index.html')
        check(target/'index.html' in landing_targets, slug+': absent from directory links')
        if not check(page is not None, slug+': missing HTML paper'):
            continue
        texpath = source/'main.tex'
        tex = texpath.read_text(encoding='utf-8')
        equation_ids, figure_ids, theorem_rows, cited = source_inventory(tex)
        for name in ('paper.pdf', 'arxiv-source.zip'):
            check((target/name).is_file() and sha(target/name) == sha(source/name),
                  slug+': published '+name+' differs from current release')
        archive = target/'arxiv-source.zip'
        if archive.is_file():
            with zipfile.ZipFile(archive) as z:
                check('main.tex' in z.namelist(), slug+': source ZIP has no root main.tex')
                if 'main.tex' in z.namelist():
                    check(z.read('main.tex') == texpath.read_bytes(), slug+': ZIP main.tex differs from current source')
        auxdir = auxroot/slug
        if not (auxdir/'main.aux').is_file():
            auxdir = auxdir/'build'
        staged = auxdir.parent/'main.tex' if auxdir.name == 'build' else auxdir/'main.tex'
        if not check((auxdir/'main.aux').is_file() and staged.is_file(), slug+': missing fresh AUX/staged source'):
            continue
        check(sha(staged) == sha(texpath), slug+': fresh AUX staging source differs')
        labels, headings, citations = aux_inventory((auxdir/'main.aux').read_text(encoding='utf-8'))
        check(not re.search(r'LaTeX Warning: (?:There were undefined references|Reference .* undefined|Citation .* undefined)',
                            (auxdir/'main.log').read_text(encoding='utf-8', errors='replace'))
              if (auxdir/'main.log').is_file() else True, slug+': fresh TeX unresolved-reference warning')
        for ident in equation_ids + figure_ids + [ident for _, ident in theorem_rows if ident]:
            check(ident in labels, slug+': source label absent from fresh AUX: '+ident)
            check(ident in page.ids, slug+': source label absent from HTML: '+ident)
            if ident in page.ids and ident in labels:
                node = page.ids[ident]
                # A label may be on a MathML row, its span, or an empty anchor.
                if not normalized(node.text()) and node.parent:
                    node = node.parent
                check(re.search(r'(?<![\dA-Za-z])'+re.escape(labels[ident])+r'(?![\dA-Za-z])', node.text()) is not None,
                      slug+': printed AUX number missing at label '+ident+' ('+labels[ident]+')')
        html_equations = {ident for ident in page.ids if ident.startswith('eq:')}
        check(html_equations == set(equation_ids), slug+': HTML/source equation-label inventory differs')
        theorem_nodes = [node for node in page.root.descendants()
                         if node.tag == 'div' and node.classes() & THEOREMS]
        check(Counter(kind for kind, _ in theorem_rows) ==
              Counter(next(iter(node.classes() & THEOREMS)) for node in theorem_nodes),
              slug+': theorem/lemma/proposition/corollary/remark inventory differs')
        actual_headings = []
        for node in page.root.descendants():
            if node.tag not in {'h2', 'h3', 'h4'}:
                continue
            match = re.match(r'^([A-Z](?:\.\d+)*|\d+(?:\.\d+)*)\s', normalized(node.text()))
            if match:
                actual_headings.append(({'h2':'section','h3':'subsection','h4':'subsubsection'}[node.tag], match[1]))
        check(actual_headings == headings, slug+': HTML heading numbering/order differs from fresh AUX')
        bbl = (auxdir/'main.bbl').read_text(encoding='utf-8')
        bblkeys = re.findall(r'\\bibitem(?:\[.*?\])?\{([^}]+)\}', bbl, re.S)
        check(set(bblkeys) == set(citations) == cited, slug+': source/AUX/BBL citation inventory differs')
        htmlrefs = {ident[4:] for ident in page.ids if ident.startswith('ref-')}
        check(htmlrefs == set(bblkeys), slug+': HTML reference inventory differs')
        cite_links = {unquote(urlsplit(url).fragment)[4:] for _, attr, url in page.links
                      if attr == 'href' and url.startswith('#ref-')}
        check(cite_links == cited, slug+': HTML citation links omit or add citation keys')
        for key, number in citations.items():
            node = page.ids.get('ref-'+key)
            if node:
                check(node.attrs.get('value') == number,
                      slug+': reference number differs from AUX: '+key)
        math_nodes = list(page.root.descendants('math'))
        body_math_nodes = []
        for node in math_nodes:
            parent, in_references = node.parent, False
            while parent:
                in_references |= parent.attrs.get('id') == 'references'
                parent = parent.parent
            if not in_references:
                body_math_nodes.append(node)
        check(bool(math_nodes), slug+': no native MathML')
        info_path = target/'format-correspondence.json'
        if check(info_path.is_file(), slug+': missing format-correspondence.json'):
            info = json.loads(info_path.read_text(encoding='utf-8'))
            check(info.get('html_sha256') == sha(page.path), slug+': stale HTML correspondence hash')
            check(info.get('aux_sha256') == sha(auxdir/'main.aux'), slug+': stale AUX correspondence hash')
            check(info.get('source_sha256', {}).get('main.tex') == sha(texpath), slug+': stale source correspondence hash')
            check(info.get('math_expressions') == len(body_math_nodes), slug+': native MathML body count differs from builder expression inventory')
        records.append({'slug':slug,'htmlSHA256':sha(page.path),'sourceSHA256':sha(texpath),
                        'auxSHA256':sha(auxdir/'main.aux'),'numberedEquations':len(equation_ids),
                        'theoremEnvironments':len(theorem_rows),'headings':len(headings),
                        'references':len(bblkeys),'nativeMathML':len(math_nodes),
                        'nativeMathMLBody':len(body_math_nodes),'nativeMathMLBibliography':len(math_nodes)-len(body_math_nodes),
                        'pdfSHA256':sha(source/'paper.pdf'),'sourceZipSHA256':sha(source/'arxiv-source.zip')})
    # Independently specified supplement allowlists; supplements never enter PAPERS.
    manifest_path = site/'release-manifest.json'
    manifest = json.loads(manifest_path.read_text(encoding='utf-8')) if manifest_path.is_file() else {}
    check([r.get('slug') for r in manifest.get('papers', [])] == list(PAPERS),
          'Release manifest must retain exactly the five manuscript records')
    expected_supplements = {
        'boundary-candidate': ('broadband-boundary-2026-10-17', 'boundary_checks.py',
            ['Earlier weak-Maxwell/operator framework', 'Strict-floor C0 frequency-uniform aperture theorem'],
            'Fixed positive band; interior center X = E* = min_B X, strict elsewhere; inf_B Gamma arbitrarily close to one.'),
        'fixed-band-candidate': ('broadband-fixed-band-2026-10-17', 'planar_checks.py',
            ['Earlier weak-Maxwell/operator framework'],
            'Fixed positive band; strict floor 0 < E_min < E*; exact center extinction E*; inf_B Gamma arbitrarily close to one.'),
    }
    supplements = manifest.get('supplements', [])
    check(len(supplements) == 2 and {r.get('id') for r in supplements} == set(expected_supplements),
          'Candidate supplement manifest inventory differs')
    for record in supplements:
        ident = record.get('id')
        if ident not in expected_supplements:
            continue
        directory, script, dependencies, claim = expected_supplements[ident]
        source = root/'papers/prescribed-extinction/research'/directory
        files = sorted(['main.tex', 'STATUS.txt', 'verification.json', script,
                        'numerical_results.json', 'verification/console.txt', 'verification/main.log'])
        check(record.get('status') == 'CANDIDATE proof' and record.get('claim_scope') == claim,
              ident+': candidate status/claim scope differs')
        check(record.get('dependencies') == dependencies, ident+': inherited dependencies differ')
        check(record.get('limitations') == 'Bandwise caps; unrestricted two-layer reciprocal tensor class; no common geometry/resource bound, linewidth floor or positive material-loss floor; no new formal verification or independent human review.',
              ident+': candidate limitations differ')
        check(record.get('source_directory') == source.relative_to(root).as_posix(), ident+': source directory differs')
        check(record.get('source_files') == files, ident+': source allowlist differs')
        check(record.get('source_sha256') == {name: sha(source/name) for name in files}, ident+': source hashes differ')
        pdf, archive = site/'prescribed-extinction'/(ident+'.pdf'), site/'prescribed-extinction'/(ident+'-source.zip')
        check(record.get('pdf') == pdf.relative_to(site).as_posix() and
              record.get('source_zip') == archive.relative_to(site).as_posix(), ident+': download paths differ')
        check(pdf.is_file() and sha(pdf) == sha(source/'research-note.pdf') == record.get('pdf_sha256') == record.get('research_pdf_sha256'),
              ident+': PDF byte identity/hash differs')
        check(archive.is_file() and sha(archive) == record.get('source_zip_sha256'), ident+': ZIP hash differs')
        if archive.is_file():
            with zipfile.ZipFile(archive) as z:
                check(z.namelist() == files, ident+': ZIP entries differ from explicit allowlist')
                for name in files:
                    if name in z.namelist():
                        check(z.read(name) == (source/name).read_bytes(), ident+': ZIP byte identity differs: '+name)
                check(all(i.date_time == (1980,1,1,0,0,0) and i.compress_type == zipfile.ZIP_STORED
                          and i.create_system == 3 and i.external_attr == 0o100644 << 16
                          for i in z.infolist()), ident+': non-deterministic ZIP metadata')
        check(pdf in landing_targets and archive in landing_targets, ident+': absent from visible landing downloads')
    scope = normalized(landing.ids['broadband-scope'].text()) if landing and 'broadband-scope' in landing.ids else ''
    for phrase in ('CANDIDATE proof', 'X(center) = E* = min_B X', 'strict inequality elsewhere',
                   'inf_B Γ is arbitrarily close to 1', 'no new formal verification or independent human review',
                   'C0 frequency-uniform aperture theorem', 'Material caps apply bandwise',
                   'resonance-linewidth floor', 'positive material-loss floor'):
        check(phrase in scope, 'Landing candidate scope missing: '+phrase)
    check('no broadband theorem or verification is claimed' not in scope,
          'Landing retains obsolete open-only broadband scope')
    builder = Path(__file__).with_name('build_pages.py')
    buildertext = builder.read_text(encoding='utf-8') if builder.is_file() else ''
    warning_policy = 'result.stderr.strip()' in buildertext and 'Pandoc conversion failed or warned' in buildertext
    check(warning_policy, 'Builder does not visibly fail closed on Pandoc stderr warnings')
    report = {'status':'passed' if not errors else 'failed',
              'createdUTC':datetime.now(timezone.utc).isoformat(),
              'scope':'Static publication format, local links, exact release identity and fresh AUX correspondence only; no scientific/proof/priority/peer-review/deployment claim.',
              'site':str(site),'auxRoot':str(auxroot),'verifierSHA256':sha(Path(__file__)),
              'builderSHA256':sha(builder) if builder.is_file() else None,
              'builderRejectsPandocStderr':warning_policy,'htmlPages':len(pages),
              'localLinksChecked':local_links,'papers':records,'errors':errors,'warnings':warnings,
              'siteFiles':{p.relative_to(site).as_posix():sha(p) for p in sorted(site.rglob('*')) if p.is_file()}}
    output = args.report.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        raise RuntimeError('Refusing to overwrite verification report: '+str(output))
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
    print(json.dumps({'status':report['status'],'errors':errors,'report':str(output)}, indent=2))
    return 0 if not errors else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--site', type=Path, default=Path(__file__).with_name('public'))
    parser.add_argument('--aux-root', type=Path, required=True)
    parser.add_argument('--base-path', default='/oq7-papers')
    parser.add_argument('--report', type=Path, required=True)
    return run(parser.parse_args())


if __name__ == '__main__':
    raise SystemExit(main())
