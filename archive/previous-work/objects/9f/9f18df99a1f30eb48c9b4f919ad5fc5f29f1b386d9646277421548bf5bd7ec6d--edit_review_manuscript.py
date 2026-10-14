from pathlib import Path
import difflib, hashlib, json, re
OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324")
p=OUT/"manuscript/main.tex"
before=p.read_text(encoding="utf-8")
old=r"Likewise, the lossless-response time-reversal bounds of Sounas and Al\`u concern a different set of hypotheses \citep{SounasAlu2017}."
new=r"Sounas and Al\`u also derive multiport and free-space response bounds, including a stated extension to loss through additional channels, as well as their lossless two-port result \citep{SounasAlu2017}. These necessary bounds do not themselves construct the prescribed-extinction dielectric family."
if before.count(old)!=1:raise RuntimeError("Expected prior-work sentence missing")
after=before.replace(old,new)
needle=r"The contribution established here is the combination of an aperture theorem uniform at vanishing physical coupling, exact finite-object extinction tuning, and positive-loss regularization preserving arbitrary fixed upper material caps. The mechanism, passive bound, extinction symmetry, and planar optical theorem have the prior precedents described above."
addition=needle+r"""

The accompanying \href{../priority/TARGETED_PRIORITY_REPORT.md}{targeted theorem-level priority comparison} separates known ingredients and routine adaptations from the potentially distinct normalized compact-localization and exact-target combination. It does not establish first priority. Full-primary access and theorem equivalence remain unresolved for the identified Mann--Al\`u and Gao--Yang--Kattawar contributions and the stated version-specific access gaps.
"""
if after.count(needle)!=1:raise RuntimeError("Contribution anchor missing")
after=after.replace(needle,addition)
anchor=r"\section{Conclusion}"
disclosure=r"""\paragraph{AI assistance and review status.}
This release used AI assistance for document preparation, source-to-claim comparison, compilation checks, and the focused literature-priority analysis. The supplied mathematical and semantic reviews are AI-assisted. Historical sources and reports retain their original version identities and attributions. No completed human peer review or independently implemented kernel check is claimed. Authorship and affiliation details are not supplied in this anonymous review copy.

"""
if after.count(anchor)!=1:raise RuntimeError("Conclusion anchor missing")
after=after.replace(anchor,disclosure+anchor)
# Preserve every mathematical environment and the whole construction/proof body.
pattern=r"\\begin\{(theorem|lemma|proposition|corollary|proof|equation)\}.*?\\end\{\1\}"
if re.findall(pattern,before,re.S)!=re.findall(pattern,after,re.S):raise RuntimeError("Math environment classes differ")
blocks_before=[m.group(0) for m in re.finditer(pattern,before,re.S)]
blocks_after=[m.group(0) for m in re.finditer(pattern,after,re.S)]
if blocks_before!=blocks_after:raise RuntimeError("Mathematical environment changed")
start=r"\section{Maxwell model, material class, and cross sections}"
end=r"\section{Formal verification"
b0=before.index(start);a0=after.index(start)
b1=before.index(end,b0);a1=after.index(end,a0)
if before[b0:b1]!=after[a0:a1]:raise RuntimeError("Mathematical exposition changed")
p.write_text(after,encoding="utf-8",newline="\n")
(OUT/"MANUSCRIPT_EDITORIAL_CHANGES.diff").write_text("".join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile="frozen/main.tex",tofile="manuscript/main.tex")),encoding="utf-8")
(OUT/"MANUSCRIPT_PRESERVATION.json").write_text(json.dumps(dict(frozen_tex_sha256=hashlib.sha256(before.encode()).hexdigest(),review_tex_sha256=hashlib.sha256(after.encode()).hexdigest(),all_math_environment_bodies_identical=True,mathematical_exposition_sections_3_to_9_identical=True,author_field="blank; anonymous review copy",changes=["Sounas 2017 scope corrected from existing primary evidence","Existing targeted priority report and limitations linked","AI-assistance and review-category disclosure added"]),indent=2),encoding="utf-8")
print("Editorial review source prepared; mathematical content preserved.")

