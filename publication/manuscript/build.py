"""Build PDF and offline MathML HTML from main.tex and references.bib.

HTML numbers and references come from the TeX-generated auxiliary files.
No scientific prose or formula is separately maintained in this converter.
"""
from pathlib import Path
import argparse
import base64
import copy
import hashlib
import html
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build"
BUILD.mkdir(exist_ok=True)

def executable(name, candidates):
    for p in candidates:
        if p.is_file():
            return str(p)
    p = shutil.which(name)
    if p:
        return p
    raise RuntimeError(f"Install {name} or place its portable executable under tools/")

def run(args, *, input_text=None, logfile=None):
    r = subprocess.run(args, cwd=ROOT, input=input_text, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    if logfile:
        logfile.write_text(r.stdout + r.stderr, encoding="utf-8")
    if r.returncode:
        raise RuntimeError(f"Command failed ({r.returncode}): {args[0]}\n{r.stderr[-3000:]}")
    return r.stdout, r.stderr

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-pdf", action="store_true", help="Use existing build/main.aux and main.bbl")
    parser.add_argument("--tectonic", help="Explicit TeX-engine path")
    parser.add_argument("--xelatex", help="Use XeLaTeX and BibTeX instead of Tectonic")
    parser.add_argument("--bibtex", default="bibtex", help="BibTeX executable for the XeLaTeX build")
    parser.add_argument("--pandoc", help="Explicit Pandoc path")
    args = parser.parse_args()
    pandoc = args.pandoc or executable("pandoc", list((ROOT / "tools/pandoc").rglob("pandoc.exe")))
    if not args.skip_pdf:
        if args.xelatex:
            latex_args = [args.xelatex, "-interaction=nonstopmode", "-halt-on-error", "-output-directory=build", "main.tex"]
            run(latex_args, logfile=BUILD / "xelatex-pass-1.log")
            run([args.bibtex, "build/main"], logfile=BUILD / "bibtex-build.log")
            run(latex_args, logfile=BUILD / "xelatex-pass-2.log")
            run(latex_args, logfile=BUILD / "xelatex-pass-3.log")
        else:
            tectonic = args.tectonic or executable("tectonic", [ROOT / "tools/tectonic/tectonic.exe"])
            os.environ.setdefault("TECTONIC_CACHE_DIR", str(ROOT / "tools/tectonic-cache"))
            run([tectonic, "--keep-logs", "--keep-intermediates", "--outdir", "build", "main.tex"],
                logfile=BUILD / "tectonic-build.log")
    for filename in ["main.pdf", "main.aux", "main.bbl"]:
        if not (BUILD / filename).is_file():
            raise RuntimeError(f"Missing TeX output: {filename}")

    aux = (BUILD / "main.aux").read_text(encoding="utf-8")
    labels = dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}", aux))
    heading_numbers = re.findall(r"\\contentsline \{(?:section|subsection)\}\{\\numberline \{([^}]+)\}", aux)
    heading_index = 0
    citations = dict(re.findall(r"\\bibcite\{([^}]+)\}\{\{(\d+)\}", aux))
    source = (ROOT / "main.tex").read_text(encoding="utf-8")
    expected_eqs = re.findall(r"\\begin\{equation\}.*?\\label\{([^}]+)\}", source, re.S)
    expected_figs = re.findall(r"\\begin\{figure\}.*?\\label\{([^}]+)\}", source, re.S)
    raw, warnings = run([pandoc, "main.tex", "-f", "latex", "-t", "json"])
    doc = json.loads(raw)
    author_names = []
    for author in doc.get("meta", {}).get("author", {}).get("c", []):
        nodes = author.get("c", [])
        name_nodes = []
        for node in nodes:
            if node.get("t") == "LineBreak":
                break
            name_nodes.append(node)
        if name_nodes:
            author_names.append({"t": "MetaInlines", "c": name_nodes})
    doc["meta"]["author-name"] = {"t": "MetaList", "c": author_names}
    equation_ids = []
    figure_ids = []
    transformed_citations = []
    math_count = 0

    def transform(value):
        nonlocal math_count, heading_index
        if isinstance(value, list):
            return [transform(v) for v in value]
        if not isinstance(value, dict):
            return value
        node = copy.deepcopy(value)
        kind = node.get("t")
        if kind == "RawInline" and node["c"][0] == "latex":
            text = node["c"][1]
            m = re.fullmatch(r"\\citep\{([^}]+)\}", text)
            if not m:
                raise RuntimeError(f"Unconverted LaTeX inline: {text}")
            keys = sorted(m.group(1).split(","), key=lambda k: int(citations[k]))
            transformed_citations.extend(keys)
            result = [{"t": "Str", "c": "["}]
            for i, key in enumerate(keys):
                if i:
                    result.append({"t": "Str", "c": ", "})
                result.append({"t": "Link", "c": [["", [], []],
                               [{"t": "Str", "c": citations[key]}], ["#ref-" + key, ""]]})
            result.append({"t": "Str", "c": "]"})
            return {"t": "Span", "c": [["", ["citation"], []], result]}
        if kind == "Link":
            attrs = dict(node["c"][0][2])
            ref = attrs.get("reference")
            if ref:
                number = labels[ref]
                if attrs.get("reference-type") == "eqref":
                    number = "(" + number + ")"
                node["c"][1] = [{"t": "Str", "c": number}]
        if kind == "Header":
            ident = node["c"][1][0]
            number = heading_numbers[heading_index]
            heading_index += 1
            if ident in labels and labels[ident] != number:
                raise RuntimeError(f"Section numbering mismatch: {ident}")
            node["c"][2] = [{"t": "Str", "c": number + " "}] + node["c"][2]
            node["c"][0] += 1  # The document title alone is h1 in the HTML.
        if kind == "Figure":
            ident = node["c"][0][0]
            figure_ids.append(ident)
            caption = node["c"][1][1][0]
            caption["c"] = [{"t": "Str", "c": "Figure " + labels[ident] + ". "}] + caption["c"]
            node["c"][2].append({"t": "Plain", "c": [{"t": "Link", "c": [
                ["", ["figure-fullsize"], [["target", "_blank"], ["rel", "noopener"]]],
                [{"t": "Str", "c": "Open full-size schematic"}],
                ["figures/two-layer-geometry.svg", "Vector schematic with readable labels"]]}]})
        if kind == "Image":
            target = node["c"][2][0]
            if target == "figures/two-layer-geometry.pdf":
                svg = ROOT / "figures/two-layer-geometry.svg"
                if not svg.is_file():
                    raise RuntimeError("Missing vector SVG counterpart for Figure 1")
                node["c"][0][2] = []
                node["c"][1] = [{"t": "Str", "c": "Finite two-layer square-aperture body: absorber below the plate, opposite z-directed incidence with common y polarization, and rotated transverse plate axis."}]
                node["c"][2][0] = "data:image/svg+xml;base64," + base64.b64encode(svg.read_bytes()).decode("ascii")
            else:
                raise RuntimeError("Unmapped figure image: " + target)
        if kind == "Div":
            ident = node["c"][0][0]
            classes = node["c"][0][1]
            if ident and any(c in classes for c in ["theorem", "lemma", "proposition", "corollary"]):
                strong = node["c"][1][0]["c"][0]
                if strong["t"] != "Strong":
                    raise RuntimeError(f"Unexpected theorem AST: {ident}")
                strong["c"][-1] = {"t": "Str", "c": labels[ident]}
        if kind == "Math":
            math_count += 1
            if node["c"][0]["t"] == "DisplayMath":
                tex = node["c"][1]
                m = re.search(r"\\label\{([^}]+)\}", tex)
                if not m:
                    raise RuntimeError("A displayed equation has no authoritative TeX label")
                ident = m.group(1)
                equation_ids.append(ident)
                tex = re.sub(r"\\label\{[^}]+\}", "", tex)
                tex = tex.replace(r"\begin{equation}", "").replace(r"\end{equation}", "").strip()
                return {"t": "Span", "c": [[ident, ["equation"], [["data-number", labels[ident]]]], [
                    {"t": "Math", "c": [{"t": "DisplayMath"}, tex]},
                    {"t": "Span", "c": [["", ["equation-number"], []], [{"t": "Str", "c": "(" + labels[ident] + ")"}]]}
                ]]}
        if kind in ["RawInline", "RawBlock"] and node.get("c", [None])[0] == "latex":
            raise RuntimeError(f"Unconverted raw LaTeX: {node}")
        return {k: transform(v) for k, v in node.items()}

    doc = transform(doc)
    if heading_index != len(heading_numbers):
        raise RuntimeError("Heading inventory differs between TeX and HTML")
    if sorted(equation_ids) != sorted(expected_eqs):
        raise RuntimeError("Equation inventory differs between TeX and HTML")
    if sorted(figure_ids) != sorted(expected_figs):
        raise RuntimeError("Figure inventory differs between TeX and HTML")
    abstract = doc["meta"].pop("abstract")["c"]
    doc["blocks"] = [{"t": "Div", "c": [["abstract", ["abstract"], []], [
        {"t": "Header", "c": [2, ["abstract-heading", [], []], [{"t": "Str", "c": "Abstract"}]]}
    ] + abstract]}] + doc["blocks"]

    bbl = (BUILD / "main.bbl").read_text(encoding="utf-8")
    matches = list(re.finditer(r"\\bibitem\[.*?\]\{([^}]+)\}", bbl, re.S))
    references = []
    for i, match in enumerate(matches):
        key = match.group(1)
        entry = bbl[match.end():matches[i+1].start() if i+1 < len(matches) else bbl.index(r"\end{thebibliography}")]
        entry = entry.replace(r"\newblock", " ").replace(r"\penalty0", "")
        entry = re.sub(r"\\doi\{([^}]+)\}", lambda m: r"\href{https://doi.org/"+m[1]+"}{doi: "+m[1]+"}", entry)
        rendered, err = run([pandoc, "-f", "latex", "-t", "html5"], input_text=entry)
        if err:
            raise RuntimeError(f"Bibliography conversion warning: {key}: {err}")
        references.append(f'<li id="ref-{html.escape(key)}" value="{citations[key]}">{rendered}</li>')
    if set(citations) != {m.group(1) for m in matches}:
        raise RuntimeError("TeX bibliography and citation numbers differ")
    doc["blocks"].append({"t": "RawBlock", "c": ["html", '<section id="references"><h2>References</h2><ol class="references">' + "\n".join(references) + '</ol></section>']})
    (BUILD / "html-source.json").write_text(json.dumps(doc, ensure_ascii=False), encoding="utf-8")
    out, math_warnings = run([pandoc, "build/html-source.json", "-f", "json", "-t", "html5", "--math-method=mathml", "--standalone", "--toc", "--toc-depth=2", "--template=template.html"])
    if math_warnings:
        raise RuntimeError("HTML math conversion warnings: " + math_warnings)
    (ROOT / "paper.html").write_text(out, encoding="utf-8")
    shutil.copyfile(BUILD / "main.pdf", ROOT / "paper.pdf")
    shutil.copyfile(BUILD / "main.bbl", ROOT / "main.bbl")
    info = dict(authoritative_sources=["main.tex", "references.bib"],
                source_sha256={n: hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in ["main.tex", "references.bib"]},
                equations=len(equation_ids), equation_labels=equation_ids, math_expressions=math_count,
                figures=len(figure_ids), figure_labels=figure_ids,
                figure_sources={n: hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
                                for n in ["figures/two-layer-geometry.pdf", "figures/two-layer-geometry.svg", "review/make_geometry.py"]},
                references=len(matches), citations=sorted(set(transformed_citations)),
                numbering_source="build/main.aux", bibliography_source="BibTeX-generated build/main.bbl",
                html_math="Native MathML; offline, no CDN; inline scroll-accessibility script only")
    (BUILD / "format-correspondence.json").write_text(json.dumps(info, indent=2), encoding="utf-8")
    print(f"Built paper.pdf and paper.html: {len(equation_ids)} equations, {len(matches)} references, {math_count} math expressions")

if __name__ == "__main__":
    main()
