"""Build the five current manuscript releases as a static GitHub Pages library.

Requires Pandoc and fresh TeX AUX/BBL outputs whose staged main.tex matches each
release. Scientific text is converted, never separately copied or summarized.
"""
from pathlib import Path
from datetime import datetime
import argparse, copy, hashlib, html, json, re, shutil, subprocess
import xml.etree.ElementTree as ET

PAPERS = [
    ('prescribed-extinction', 'Prescribed extinction', 'A single-frequency unit supremum at exactly prescribed positive extinction, without a common size or volume bound.'),
    ('generalized-research', 'Channels and thickness', 'Sharp channel tradeoffs and scalar dielectric thickness asymptotics.'),
    ('quartic-maxwell', 'Quartic bounds', 'Uniform small-object bounds for opposite real linear polarizations.'),
    ('fixed-resource-bounds', 'Resource bounds', 'Response budgets, radiation spectra, and fixed-resource bounds.'),
    ('compact-maxwell-cross-sections', 'Compact localization', 'Finite-aperture localization and dipolar bounds for compact objects.'),
]
THEOREMS = {'theorem', 'lemma', 'proposition', 'corollary', 'remark'}
MATH_NS = 'http://www.w3.org/1998/Math/MathML'
ET.register_namespace('', MATH_NS)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def pandoc_run(exe, args, input_text=None):
    result = subprocess.run([str(exe), *args], input=input_text, capture_output=True,
                            text=True, encoding='utf-8', errors='replace')
    if result.returncode or result.stderr.strip():
        raise RuntimeError(f'Pandoc conversion failed or warned: {result.stderr}')
    return result.stdout

def str_node(text):
    return {'t': 'Str', 'c': text}

def span(ident, classes, content):
    return {'t': 'Span', 'c': [[ident, classes, []], content]}

def plain_text(nodes):
    if isinstance(nodes, list):
        return ''.join(plain_text(x) for x in nodes)
    if not isinstance(nodes, dict):
        return ''
    if nodes.get('t') in {'Str', 'Code', 'Math'}:
        return nodes['c'] if nodes['t'] == 'Str' else nodes['c'][-1]
    if nodes.get('t') in {'Space', 'SoftBreak', 'LineBreak'}:
        return ' '
    return plain_text(nodes.get('c', []))

def split_align_rows(text):
    """Split outer AMS rows while retaining nested matrices/cases/aligned."""
    depth, start, rows = 0, 0, []
    for match in re.finditer(r'\\begin\{[^}]+\}|\\end\{[^}]+\}|\\\\(?:\[[^]]*\])?', text):
        token = match[0]
        if token.startswith(r'\begin'):
            depth += 1
        elif token.startswith(r'\end'):
            depth -= 1
        elif depth == 0:
            rows.append(text[start:match.start()])
            start = match.end()
    if text[start:].strip():
        rows.append(text[start:])
    return rows

def normalize_math(tex):
    # Equivalent modern math spelling for legacy TeX font declarations.
    tex = re.sub(r'\{\\rm\s+([^{}]*)\}', lambda m: r'\mathrm{' + m[1] + '}', tex)
    # Pandoc expands the one-token \dd numerator before parsing \frac. Restore
    # its braces; the manuscript's \frac\dd{\dd z} still denotes d/dz.
    tex = tex.replace(r'\frac\,\mathrm d{', r'\frac{\,\mathrm{d}}{')
    return tex

def build_paper(root, out, aux_root, exe, slug):
    source = root / 'papers' / slug / 'arxiv'
    aux_dir = aux_root / slug
    if not (aux_dir / 'main.aux').exists():
        aux_dir = aux_dir / 'build'
    staged = aux_dir.parent / 'main.tex' if aux_dir.name == 'build' else aux_dir / 'main.tex'
    if sha(staged) != sha(source / 'main.tex'):
        raise RuntimeError('AUX source mismatch: ' + slug)
    aux = (aux_dir / 'main.aux').read_text(encoding='utf-8')
    bbl = (aux_dir / 'main.bbl').read_text(encoding='utf-8')
    labels = dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}', aux))
    headings = re.findall(r'\\contentsline \{(section|subsection|subsubsection)\}\{\\numberline \{([^}]+)\}', aux)
    citations = dict(re.findall(r'\\bibcite\{([^}]+)\}\{\{(\d+)\}', aux))
    raw = pandoc_run(exe, [str(source / 'main.tex'), '-f', 'latex', '-t', 'json'])
    doc = json.loads(raw)
    title = plain_text(doc['meta']['title']['c']).strip()
    date = plain_text(doc['meta']['date']['c']).strip()
    target = out / slug
    target.mkdir(parents=True, exist_ok=True)
    heading_index, section, theorem_count, math_count = 0, '', 0, 0
    equation_ids, figure_ids, used_cites, theorem_numbers = [], [], [], {}

    def align_html(tex):
        all_labels = re.findall(r'\\label\{([^}]+)\}', tex)
        inner = re.sub(r'^\s*\\begin\{align\}|\\end\{align\}\s*$', '', tex)
        rows = split_align_rows(inner)
        numbered = [i for i, row in enumerate(rows) if not re.search(r'\\(?:notag|nonumber)\b', row)]
        row_info = {}
        for i in numbered:
            row_labels = re.findall(r'\\label\{([^}]+)\}', rows[i])
            if not row_labels and len(numbered) == 1 and len(all_labels) == 1:
                row_labels = all_labels
            if len(row_labels) != 1:
                raise RuntimeError('Numbered align row lacks one authoritative label: ' + slug)
            ident = row_labels[0]
            row_info[i] = (ident, labels[ident])
        if sorted(x[0] for x in row_info.values()) != sorted(all_labels):
            raise RuntimeError('Align label inventory mismatch')
        cleaned = re.sub(r'\\label\{[^}]+\}|\\(?:notag|nonumber)\b', '', inner)
        math_doc = {'pandoc-api-version': doc['pandoc-api-version'], 'meta': {},
                    'blocks': [{'t': 'Para', 'c': [{'t': 'Math', 'c': [{'t': 'DisplayMath'}, r'\begin{aligned}' + cleaned + r'\end{aligned}']}]}]}
        rendered = pandoc_run(exe, ['-f', 'json', '-t', 'html5', '--math-method=mathml'], json.dumps(math_doc))
        math = ET.fromstring(re.search(r'(<math\b.*?</math>)', rendered, re.S)[1])
        table = math.find(f'./{{{MATH_NS}}}semantics/{{{MATH_NS}}}mtable')
        if table is None or len(table) != len(rows):
            raise RuntimeError('Align MathML row inventory mismatch')
        for i, row in enumerate(table):
            cell = ET.SubElement(row, f'{{{MATH_NS}}}mtd', {'class': 'align-number', 'style': 'padding-left:2em;text-align:right'})
            if i in row_info:
                ident, number = row_info[i]
                row.set('id', ident)
                ET.SubElement(cell, f'{{{MATH_NS}}}mtext').text = '(' + number + ')'
                equation_ids.append(ident)
        return '<span class="equation align-equation" tabindex="0" aria-label="Aligned equations">' + ET.tostring(math, encoding='unicode') + '</span>'

    def transform(value):
        nonlocal heading_index, section, theorem_count, math_count
        if isinstance(value, list):
            return [transform(v) for v in value]
        if not isinstance(value, dict):
            return value
        node = copy.deepcopy(value)
        kind = node.get('t')
        if kind == 'Cite':
            records = node['c'][0]
            used_cites.extend(x['citationId'] for x in records)
            ids = sorted((x['citationId'] for x in records), key=lambda key: int(citations[key]))
            links = []
            for i, key in enumerate(ids):
                if i:
                    links.append(', ')
                links.append(f'<a href="#ref-{html.escape(key)}">{citations[key]}</a>')
            # Natbib optional arguments are part of the source citation, e.g. Sec. 3.1.
            raw_cite = node['c'][1][0]['c'][1]
            optional = re.findall(r'\[([^]]*)\]', raw_cite)
            prefix, suffix = ('', '')
            if len(optional) == 1:
                suffix = optional[0]
            elif len(optional) == 2:
                prefix, suffix = optional
            def prose(text):
                return pandoc_run(exe, ['-f', 'latex', '-t', 'html5'], text).strip().removeprefix('<p>').removesuffix('</p>') if text else ''
            text = '[' + (prose(prefix) + ' ' if prefix else '') + ''.join(links) + (', ' + prose(suffix) if suffix else '') + ']'
            return {'t': 'RawInline', 'c': ['html', '<span class="citation">' + text + '</span>']}
        if kind == 'Link':
            attrs = dict(node['c'][0][2])
            if attrs.get('reference'):
                ref = attrs['reference']
                number = labels[ref]
                node['c'][1] = [str_node('(' + number + ')' if attrs.get('reference-type') == 'eqref' else number)]
        if kind == 'Header':
            if node['c'][0] > 3:
                # LaTeX paragraph headings have no section number or TOC entry.
                return {'t': 'Para', 'c': [{'t': 'Strong', 'c': transform(node['c'][2])}]}
            expected_kind, number = headings[heading_index]
            if node['c'][0] != {'section': 1, 'subsection': 2, 'subsubsection': 3}[expected_kind]:
                raise RuntimeError('Section depth mismatch')
            heading_index += 1
            if node['c'][0] == 1:
                section, theorem_count = number, 0
            ident = node['c'][1][0]
            if ident in labels and labels[ident] != number:
                raise RuntimeError('Section label mismatch')
            node['c'][2] = [str_node(number + ' ')] + node['c'][2]
            node['c'][0] += 1
        if kind == 'Div' and THEOREMS.intersection(node['c'][0][1]):
            theorem_count += 1
            ident = node['c'][0][0]
            number = section + '.' + str(theorem_count)
            if ident and labels[ident] != number:
                raise RuntimeError('Theorem numbering mismatch: ' + ident)
            if not ident:
                ident = 'statement-' + number
                node['c'][0][0] = ident
            strong = node['c'][1][0]['c'][0]
            if strong['t'] not in {'Strong', 'Emph'}:
                raise RuntimeError('Unexpected theorem heading')
            strong['c'][-1] = str_node(number)
            theorem_numbers[ident] = number
        if kind == 'Figure':
            ident = node['c'][0][0]
            figure_ids.append(ident)
            caption = node['c'][1][1][0]
            caption['c'] = [str_node('Figure ' + labels[ident] + '. ')] + caption['c']
        if kind == 'Image':
            image = node['c'][2][0]
            if image != 'figures/two-layer-geometry.pdf':
                raise RuntimeError('Unexpected figure: ' + image)
            svg = root / 'papers' / slug / 'publication/manuscript/figures/two-layer-geometry.svg'
            (target / 'figures').mkdir(exist_ok=True)
            shutil.copyfile(svg, target / 'figures/two-layer-geometry.svg')
            node['c'][2][0] = 'figures/two-layer-geometry.svg'
            node['c'][0][2] = []
            node['c'][1] = [str_node('Two-layer compact dielectric geometry: absorber and rotated waveplate, illuminated from opposite sides with the same linear polarization.')]
        if kind == 'Math':
            math_count += 1
            node['c'][1] = normalize_math(node['c'][1])
            node['c'][1] = re.sub(r'\\(eqref|ref)\{([^}]+)\}',
                lambda m: r'\text{' + ('(' + labels[m[2]] + ')' if m[1] == 'eqref' else labels[m[2]]) + '}', node['c'][1])
            if node['c'][0]['t'] == 'DisplayMath':
                tex = node['c'][1]
                if r'\begin{align}' in tex:
                    return {'t': 'RawInline', 'c': ['html', align_html(tex)]}
                ids = re.findall(r'\\label\{([^}]+)\}', tex)
                if len(ids) > 1:
                    raise RuntimeError('Multiple labels in one display')
                tex = re.sub(r'\\label\{[^}]+\}', '', tex)
                tex = re.sub(r'\\(?:begin|end)\{equation\*?\}', '', tex).strip()
                node['c'][1] = tex
                if ids:
                    ident = ids[0]
                    equation_ids.append(ident)
                    return span(ident, ['equation'], [node, span('', ['equation-number'], [str_node('(' + labels[ident] + ')')])])
                return span('', ['equation', 'unnumbered'], [node])
        if kind in {'RawInline', 'RawBlock'} and node['c'][0] == 'latex':
            raise RuntimeError('Unconverted LaTeX: ' + repr(node))
        return {k: transform(v) for k, v in node.items()}

    doc = transform(doc)
    if heading_index != len(headings):
        raise RuntimeError('Heading count mismatch')
    tex = (source / 'main.tex').read_text(encoding='utf-8')
    expected_eqs = re.findall(r'\\label\{(eq:[^}]+)\}', tex)
    if sorted(expected_eqs) != sorted(equation_ids):
        raise RuntimeError('Equation inventory mismatch for ' + slug)
    expected_figures = re.findall(r'\\label\{(fig:[^}]+)\}', tex)
    if sorted(expected_figures) != sorted(figure_ids):
        raise RuntimeError('Figure inventory mismatch')
    abstract = doc['meta'].pop('abstract')['c']
    doc['blocks'] = [{'t': 'Div', 'c': [['abstract', ['abstract'], []], [{'t': 'Header', 'c': [2, ['abstract-heading', [], []], [str_node('Abstract')]]}] + abstract]}] + doc['blocks']
    entries = list(re.finditer(r'\\bibitem\[.*?\]\{([^}]+)\}', bbl, re.S))
    references = []
    for i, match in enumerate(entries):
        key = match[1]
        entry = bbl[match.end():entries[i+1].start() if i+1 < len(entries) else bbl.index(r'\end{thebibliography}')]
        entry = entry.replace(r'\newblock', ' ').replace(r'\penalty0', '')
        entry = re.sub(r'\\doi\{([^}]+)\}', lambda m: r'\href{https://doi.org/' + m[1] + '}{doi: ' + m[1] + '}', entry)
        rendered = pandoc_run(exe, ['-f', 'latex', '-t', 'html5'], entry)
        references.append(f'<li id="ref-{html.escape(key)}" value="{citations[key]}">{rendered}</li>')
    if set(citations) != {x[1] for x in entries}:
        raise RuntimeError('Bibliography inventory mismatch')
    doc['blocks'].append({'t': 'RawBlock', 'c': ['html', '<section id="references"><h2>References</h2><ol class="references">' + '\n'.join(references) + '</ol></section>']})
    body = pandoc_run(exe, ['-f', 'json', '-t', 'html5', '--math-method=mathml', '--toc', '--toc-depth=2', '--standalone', '--template=' + str(Path(__file__).with_name('paper-template.html'))], json.dumps(doc, ensure_ascii=False))
    (target / 'index.html').write_text(body, encoding='utf-8')
    for name in ['paper.pdf', 'arxiv-source.zip']:
        shutil.copyfile(source / name, target / name)
    info = {'slug': slug, 'title': title, 'date': date,
            'source_directory': f'papers/{slug}/arxiv',
            'source_sha256': {name: sha(source / name) for name in ['main.tex', 'references.bib', 'main.bbl', 'paper.pdf', 'arxiv-source.zip']},
            'html_sha256': sha(target / 'index.html'), 'aux_sha256': sha(aux_dir / 'main.aux'),
            'bbl_sha256': sha(aux_dir / 'main.bbl'), 'math_expressions': math_count,
            'equation_labels': equation_ids, 'theorem_numbers': theorem_numbers,
            'figures': figure_ids, 'references': len(entries), 'cited_keys': sorted(set(used_cites)),
            'html_math': 'Native MathML, no remote scripts or fonts', 'numbering_source': 'fresh exact-source TeX AUX'}
    (target / 'format-correspondence.json').write_text(json.dumps(info, indent=2) + '\n', encoding='utf-8')
    return info

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--pandoc', type=Path, required=True)
    parser.add_argument('--aux-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('public'))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    records = [build_paper(args.root, args.output, args.aux_root, args.pandoc, slug) for slug, _, _ in PAPERS]
    rows = []
    for i, (record, (slug, short, description)) in enumerate(zip(records, PAPERS), 1):
        rows.append(f'''<article class="paper-row"><div class="paper-number">{i:02}</div><div class="paper-info"><p class="paper-topic">{html.escape(short)}</p><h2><a href="{slug}/">{html.escape(record['title'])}</a></h2><p class="paper-description">{html.escape(description)}</p><p class="paper-date">{html.escape(record['date'])}</p><nav class="paper-links" aria-label="{html.escape(short)} formats"><a class="read-link" href="{slug}/">Read HTML <span aria-hidden="true">↗</span></a><a href="{slug}/paper.pdf">PDF</a><a href="{slug}/arxiv-source.zip" download>Source ZIP</a></nav></div></article>''')
    template = Path(__file__).with_name('index-template.html').read_text(encoding='utf-8')
    (args.output / 'index.html').write_text(template.replace('<!-- PAPER_ROWS -->', '\n'.join(rows)), encoding='utf-8')
    shutil.copyfile(Path(__file__).with_name('style.css'), args.output / 'style.css')
    (args.output / '.nojekyll').write_text('', encoding='utf-8')
    edition = max(datetime.strptime(record['date'], '%d %B %Y').date() for record in records).isoformat()
    manifest = {'edition': edition, 'edition_basis': 'Latest manuscript date; individual manuscript dates are recorded below.',
                'scope': 'Five current manuscript releases; broadband directions are open research targets, with no new scientific verification or peer-review claim.',
                'pandoc_version': pandoc_run(args.pandoc, ['--version']).splitlines()[0], 'papers': records}
    (args.output / 'release-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    print(json.dumps([{'paper': r['slug'], 'equations': len(r['equation_labels']), 'references': r['references']} for r in records]))

if __name__ == '__main__':
    main()
