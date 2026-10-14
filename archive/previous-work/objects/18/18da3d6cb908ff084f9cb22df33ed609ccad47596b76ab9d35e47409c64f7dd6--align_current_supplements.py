from pathlib import Path
import json,shutil
OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324")
repro=OUT/"manuscript/reproducibility"
shutil.copy2(OUT/"supplements/S4_AUDIT_PROVENANCE.md",repro/"AUDIT_PROVENANCE.md")
shutil.copy2(OUT/"verification/CURRENT_VERIFICATION.json",repro/"current-verification.json")
index="""<!doctype html><html><head><meta charset="utf-8"><title>OQ7 S1-S4 and verification evidence</title></head><body>
<h1>Review supplements</h1>
<p>Audited proof commit: <code>686402a6c2d63820828729cc7ab02504632e3fe7</code>. Complete final audit evidence is recovered. Historical files are retained as historical files.</p>
<ul>
<li>S1: <a href="../theorem-correspondence.csv">claim-to-code CSV</a> and <a href="../theorem-correspondence.html">readable correspondence</a>.</li>
<li>S2: <a href="OQ7-complete-physical-theorem11-source.zip">exact frozen source</a> and <a href="OQ7-complete-physical-theorem11.bundle">complete Git bundle</a>.</li>
<li>S3: <a href="manifest.json">unchanged frozen verification manifest</a>, <a href="final-audit-status.json">completed final audit status</a> and <a href="current-verification.json">regenerated checks and fresh same-kernel replay</a>.</li>
<li>S4: <a href="AUDIT_PROVENANCE.md">current provenance and review categories</a>, <a href="AUDIT_REPORT_686402a.md">completed final audit report</a> and <a href="MANUSCRIPT_VERSION_CORRESPONDENCE.md">Theorem 1.1 to 4.1 version map</a>.</li>
<li><a href="../../REPRODUCE.md">Reproduction commands</a> and <a href="../../FINAL_REVIEW_AUDIT.md">final package audit</a>.</li>
<li><a href="../../priority/TARGETED_PRIORITY_REPORT.md">existing targeted priority comparison</a>: first priority unresolved.</li>
</ul>
<p>The final main theorem uses only propext, Classical.choice and Quot.sound. Fresh replay uses Lean's same kernel; human peer review and an independently implemented kernel checker are not established. The anonymous review PDF does not supply author/affiliation metadata.</p></body></html>"""
(repro/"SUPPLEMENT_INDEX.html").write_text(index,encoding="utf-8")
print("Current manuscript supplement targets aligned; historical versions preserved in release/.")

