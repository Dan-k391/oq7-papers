from pathlib import Path
import datetime,hashlib,json,re,shutil
OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324");WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\s0c32f324")
status=json.loads((OUT/"verification/CURRENT_VERIFICATION.json").read_text(encoding="utf-8"))
if status["status"]!="PASS":raise RuntimeError("Verification did not pass")
records=[json.loads(line) for line in (OUT/"verification/COMMANDS.jsonl").read_text(encoding="utf-8").splitlines()]
replay=next(r for r in records if r["label"]=="KERNEL_REPLAY")
elapsed=(datetime.datetime.fromisoformat(replay["finished_utc"])-datetime.datetime.fromisoformat(replay["started_utc"])).total_seconds()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
current=status|dict(kernel_replay_exit_code=replay["exit_code"],kernel_replay_started_utc=replay["started_utc"],kernel_replay_finished_utc=replay["finished_utc"],kernel_replay_elapsed_seconds=elapsed,main_dependency_axioms=["propext","Classical.choice","Quot.sound"],forbidden_axioms_present_in_imported_environment_but_outside_final_cone=["sorryAx","Lean.ofReduceBool","Lean.trustCompiler"],human_peer_review_established=False,scientific_first_priority_established=False)
(OUT/"verification/CURRENT_VERIFICATION.json").write_text(json.dumps(current,indent=2),encoding="utf-8")
for src,dst in [("verification/FINAL_THEOREM_TYPE.log","FINAL_THEOREM_TYPE.txt"),("verification/FINAL_AXIOMS.log","FINAL_AXIOMS.txt"),("verification/KERNEL_REPLAY.log","KERNEL_REPLAY.log"),("verification/CURRENT_VERIFICATION.json","supplements/S3_CURRENT_VERIFICATION.json"),("release/portable-test-logs/project-build.log","HISTORICAL_CLEAN_BUILD.log")]:
    shutil.copy2(OUT/src,OUT/dst)
p=OUT/"MANUSCRIPT_PRESERVATION.json";data=json.loads(p.read_text(encoding="utf-8"))
data.update(frozen_tex_sha256=sha(OUT/"frozen/main.tex"),review_tex_sha256=sha(OUT/"manuscript/main.tex"),frozen_pdf_sha256=sha(OUT/"frozen/paper.pdf"),review_pdf_sha256=sha(OUT/"manuscript/paper.pdf"),comparison_basis="UTF-8 text with line endings normalized for mathematical-content preservation; all SHA-256 fields identify actual raw file bytes.")
p.write_text(json.dumps(data,indent=2),encoding="utf-8")
for name in ["supplements/S4_AUDIT_PROVENANCE.md","AUDIT_PROVENANCE.md"]:
    p=OUT/name;s=p.read_text(encoding="utf-8")
    s=s.replace("plus current verification/KERNEL_REPLAY.log and command record when completed","plus the completed current verification/KERNEL_REPLAY.log and exact command record (exit 0)")
    s=s.replace("A new same-kernel replay, if completed, is recorded explicitly in CURRENT_VERIFICATION.json rather than inferred from an earlier pass.","The new same-kernel replay passed with exit 0 in "+f"{elapsed:.3f}"+" seconds and is recorded explicitly in CURRENT_VERIFICATION.json; it is not inferred from an earlier pass.")
    p.write_text(s,encoding="utf-8")
warn=(OUT/"verification/REGENERATED_BUILD.log").read_text(encoding="utf-8")
warnings=[line for line in warn.splitlines() if line.startswith("warning:")]
(OUT/"verification/BUILD_WARNINGS.txt").write_text("\n".join(warnings)+"\n",encoding="utf-8")
strict="""# Strict verification boundary

The regenerated final-theorem axiom report contains only propext, Classical.choice and Quot.sound. The exhaustive project sweep reports the same allowed set for every project constant.

The cone report explicitly flags sorryAx, Lean.ofReduceBool and Lean.trustCompiler as **present in the imported environment but outside the final theorem's dependency cone**. Their existence in Lean's imported infrastructure is not hidden. None is a dependency of the final theorem, and none occurs in the project-wide reachable-axiom set. No additional mathematical axiom, admitted proof or native-trust axiom is accepted for the strict main claim.

The new fresh replay succeeded with exit 0 for PrescribedExtinction.PhysicalTheorem11. The pinned helper loads that module and replays its import environment into an empty Lean kernel environment. This is the same Lean kernel implementation. Its native/unsafe IO driver is not an independently implemented mathematical checker and does not change the axiom census.

An independently implemented checker was not supplied or run. Human peer review is not established. The current build reused compatible objects; the preserved earlier clean build and this new fresh replay are distinct pieces of evidence.
"""
(OUT/"verification/STRICT_VERIFICATION_SCOPE.md").write_text(strict,encoding="utf-8")
audit=f"""# Final review-package audit

Date: 13 October 2026. This is a targeted evidence/package audit. No new research, general OQ7 investigation, proof restart, human audit or independent-kernel checker was commissioned.

**Disposition:** the compact prescribed-extinction theorem's supported formal-verification claim is retained. Exact final source is recovered, all 378 mathematical modules match the audited archive, the pinned reproduction checks pass, and the new same-kernel fresh replay passes. The anonymous manuscript is ready to circulate for review. Named journal-submission metadata remains incomplete.

## Completed checks in this run

- Verified the existing release SHA-256 manifest before copying it; historical reports and manuscripts are preserved.
- Checked all nine pinned dependency revisions and clean tracked sources, and the exact compiler version/commit.
- Regenerated the 3,601-job Lake target check in a new isolated checkout using compatible cached dependency/project objects. This is not described as a new from-source clean build.
- Regenerated the fully elaborated final type and its defining statement/material/state structures; retained exact diagnostic programs and complete output.
- Regenerated the final-theorem dependency-axiom report: only propext, Classical.choice and Quot.sound.
- Checked every one of the 52 OQ7Prescribed names in the correspondence CSV; reran all four preserved auditor programs.
- Reran the main-cone and exhaustive project axiom audits. The whole-project sweep reports 5,658 roots, 49 private, with 68,675 union dependencies and only the three allowed foundation axioms.
- Freshly replayed PrescribedExtinction.PhysicalTheorem11 into an empty environment using the same pinned Lean kernel: exit {replay['exit_code']}, {elapsed:.3f} seconds. Complete logs/commands are supplied.
- Inspected all 16 rendered PDF pages, with full-page checks of the main theorem, diagram, verification/disclosure and bibliography.
- Checked 20 bibliography entries/20 cited keys, 71 unique TeX labels, 83 resolving HTML internal links, local supplement links and all 51 equations. No undefined citation/reference or overfull-box warning remains.
- Preserved all mathematical environment bodies and the full mathematical exposition of Sections 3–9. The frozen paper remains byte-preserved; the review revision corrects Sounas 2017 attribution, links the already-completed priority comparison and adds AI-assistance disclosure.

The first document-conversion attempt failed on an unsupported paragraph-level heading in the HTML numbering converter. That formatting was changed to bold paragraph text; the successful second build and the failed attempt are both logged. No mathematical repair was made. The current build retains {len(warnings)} warning lines in BUILD_WARNINGS.txt; full diagnostics remain in REGENERATED_BUILD.log.

## Scientific scope retained

Gamma is the absolute absorption difference divided by common dimensional extinction, equivalently the scattering difference divided by it. Incident waves have the same real y polarization and unit electric amplitude and propagate along ±z. One unchanged object/material law is used for both experiments; the two layers can have different tensors.

For fixed k>0, every fixed P>1,Q>0, every exact E*>0 and every accuracy in (0,1), the witness is a finite compact square-aperture two-layer local reciprocal anisotropic dielectric with mu=I, vacuum exterior and the stated Hermitian caps. Radiation accounting includes the complete outgoing sphere and both transverse polarizations, with canonical exterior representatives for sphere flux. The target equality is exact, not a numerical tolerance.

Each witness has finite positive dimensions and strictly positive tensor loss. No common dimension/resource ceiling or positive loss floor is imposed across the approximating sequence. Both suprema hold in that full stated class, with strict nonattainment. No fixed-resource optimum, bandwidth guarantee, experimental realization, arbitrary-shape theorem or every-OQ7 claim is added.

## Version-specific disposition and review categories

The old thickness checkpoint is uncompiled evidence, and the 43-authored-theorem finite-port source package is not recovered. Neither supports the final Maxwell claim. Later scalar and partial mission packages remain separate. The exact OQ7Prescribed complete declaration at 686402a6c2d63820828729cc7ab02504632e3fe7 is the formal basis here; the ordinary-only fallback is not triggered.

The final recovered AI-assisted audit reports main-theorem semantic/model PASS and F1–F4 closure. The preserved ordinary mathematical consistency report reviews its identified corrections/revision. These are completed evidence, not human peer-review certificates or certification of every line of this reorganized proof presentation. The historical earlier FAIL/pending/unrecovered statements remain intact and are mapped to their actual earlier versions.

The completed priority investigation is bounded and AI-assisted. It identifies a potentially distinct normalized compact-localization/exact-target combination and specific primary-access/equivalence gaps; it does not establish first priority. No new priority search was performed for this package.

No independently implemented kernel checker or completed human peer review is fabricated. Author/affiliation facts are not supplied; the paper stays anonymous. The Gmail sender identity is a transmission choice, not authorship evidence.

## Files and identities

- Frozen proof commit: 686402a6c2d63820828729cc7ab02504632e3fe7.
- Portable packaging commit: 0bdf00f9b75b43194436f9536b1bf09463fd5a5d.
- Frozen release paper SHA-256: {sha(OUT/'frozen/paper.pdf')}.
- Review paper SHA-256: {sha(OUT/'manuscript/paper.pdf')}.
- Review source SHA-256: {sha(OUT/'manuscript/main.tex')}.
- S1–S4 are actual files in supplements/, with the manuscript's matching local supplement files retained.
- SHA256SUMS identifies package content; archive hashes are separate to avoid self-reference.

Sending the paper to denialk391@gmail.com is explicitly authorized by the user after these checks. Two connected Gmail accounts are exposed, and the sender choice must be resolved before the mail tool can send. No journal submission, preprint upload, publication, or other contact is authorized or performed.
"""
(OUT/"FINAL_REVIEW_AUDIT.md").write_text(audit,encoding="utf-8")
index="""# Final OQ7 prescribed-extinction review package

The completed audited source is preserved, and the targeted finalization checks pass. The primary paper remains focused on the compact prescribed-extinction supremum. No new research was added.

## Main deliverables

- manuscript/paper.pdf and main.tex: checked 16-page review revision, bibliography and assets.
- frozen/paper.pdf and main.tex: byte-preserved completed-audit release version.
- supplements/S1_THEOREM_CORRESPONDENCE.md, .csv and .html: statement/claim-to-code scope.
- supplements/S2_FROZEN_SOURCE.zip and .bundle: exact audited repository export and full Git bundle.
- supplements/S3_FROZEN_VERIFICATION_MANIFEST.json: immutable historical manifest.
- supplements/S3_CURRENT_VERIFICATION.json: current checks, exact pins and replay status.
- supplements/S4_AUDIT_PROVENANCE.md: actual review identities, commits and categories.
- release/dependency-sources/: all nine pinned dependency source/Git snapshots.
- toolchain/lean-4.34.1-windows.zip: exact pinned official compiler archive.
- FINAL_THEOREM_TYPE.txt, FINAL_AXIOMS.txt, KERNEL_REPLAY.log and verification/: regenerated programs, complete logs, commands and versions.
- HISTORICAL_CLEAN_BUILD.log: preserved earlier clean project build; distinct from the current cached/incremental run.
- CLAIM_TO_CODE.md, VERSION_VERIFICATION_DISPOSITION.md, AUDIT_PROVENANCE.md and FINAL_REVIEW_AUDIT.md: current evidence map and final audit.
- reviews/, historical/ and release/evidence/: unrewritten original reports and manuscripts.
- priority/: the already-completed targeted comparison and limitations.
- REPRODUCE.md and SHA256SUMS: reproduction and content identities.

## Supported status

The final OQ7Prescribed proof/source recovery, strict axiom checking, completed main-statement semantic audit and fresh same-kernel replay are supported. AI-assisted mathematical review has its stated scope. Human peer review and independently implemented kernel checking are not established. Priority analysis is completed as a bounded investigation; first priority is unresolved.

The old uncompiled thickness checkpoint and missing 43-theorem finite-port supplement are explicitly separated from the final Maxwell theorem. Their historical claims do not substitute for recovered source.

The paper is anonymous: name, affiliation, ORCID and corresponding-author metadata are not supplied. It is a review package, not a completed named journal submission. AI assistance is disclosed. No publication, preprint upload or journal submission has occurred.

The complete archive includes the pinned Windows compiler and dependency sources. The smaller email review packet includes the paper/source, S1–S4, reports and checking instructions; it does not include the 850 MB compiler binary or dependency source archives. The user authorized sending the paper to denialk391@gmail.com; transmission is recorded separately after the Gmail sender account is selected.
"""
(OUT/"REVIEW_INDEX.md").write_text(index,encoding="utf-8")
email="""<!doctype html><html><body>
<p>Hello,</p>
<p>Attached are <em>Unit Absorption Asymmetry at Prescribed Extinction for Compact Reciprocal Dielectrics</em> and its review materials.</p>
<p>The paper concerns the compact prescribed-extinction supremum at one frequency, with the same unchanged local reciprocal nonmagnetic dielectric object for both opposite, equally polarized incident waves. It keeps the exact extinction target, full radiation accounting, pointwise material caps, unrestricted dimensions across the sequence, absence of a common positive loss floor, and strict nonattainment explicit.</p>
<p>The frozen source commit is <code>686402a6c2d63820828729cc7ab02504632e3fe7</code>. The completed audit evidence is preserved. The finalization checks regenerated the theorem type and standard-axiom reports, reran the preserved auditor programs, and successfully performed fresh replay through the same Lean kernel. Human peer review and an independently implemented kernel checker are not claimed.</p>
<p>The priority report is a bounded comparison and does not establish first priority. This is an anonymous review copy because author and affiliation details have not been supplied. AI assistance is disclosed. No journal submission or preprint publication has been made.</p>
<p>The attached review packet contains the manuscript source, S1–S4, frozen Lean source, reports, logs and reproduction instructions. The full local package also contains the pinned compiler/dependency archives, which are omitted from the email-sized packet.</p>
</body></html>"""
(OUT/"EMAIL_PREVIEW.html").write_text(email,encoding="utf-8")
print("CURRENT_DOCS_FINALIZED",f"same-kernel replay {elapsed:.3f}s",len(warnings),"warning lines")

