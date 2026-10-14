import csv,hashlib,html,json,pathlib
root=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1'); work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\r59a36c60'); out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-release-20261013-final-audit-59a36c60')
def put(name,text): p=out/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text.strip()+'\n',encoding='utf-8')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
original_pdf=root/'outputs/oq7-prescribed-extinction/sources/OQ7_prescribed_extinction_2026-10-11.pdf'
current_pdf=root/'outputs/oq7-paper1-publication/paper.pdf'
preceding=out/'evidence/preceding/AUDIT_REPORT_5a8350d.md'
put('MANUSCRIPT_VERSION_CORRESPONDENCE.md',f"""
# Manuscript version correspondence

Audited formal authority: commit `686402a6c2d63820828729cc7ab02504632e3fe7`, tree `580737ccf6557102d601894145cc0229ae1f83e3`; declaration `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement`.

| Manuscript | Content identity | Main statements |
|---|---|---|
| Audited October 11 specification, 19 pages | SHA-256 `{digest(original_pdf)}`; exact copy in evidence/manuscripts/ | Theorem 1.1 and Lemma 1.2, PDF page 3 |
| Newer publication baseline, 16 pages | SHA-256 `{digest(current_pdf)}`; preserved in evidence/publication-baseline/ | Theorem 4.1 and Lemma 4.2, PDF page 4 |
| Release manuscript | manuscript/main.tex and manuscript/paper.pdf; exact identities in SHA256SUMS | Same Theorem 4.1 and Lemma 4.2; formal-status prose updated |

## Precise main-statement mapping

| Audited October 11 content | Newer publication content | Assessment |
|---|---|---|
| k>0, P>1, Q>0, every E_*>0, every 0<epsilon<1 | Identical quantified parameter ranges in Theorem 4.1 | No substantive change |
| Two adjacent homogeneous anisotropic dielectric layers; common finite square aperture in vacuum | Section 3 and Theorem 4.1 explicitly use finite positive R,h,d and the two-layer square-aperture class | Same formal geometry; more explicit positivity and coordinate convention |
| Relative permeability I; transpose reciprocity; I <= Re_H epsilon <= PI; 0 < Im_H epsilon <= QI, Eq. (3) | Same material conditions, Eq. (2) | No substantive change; no common positive loss floor added |
| Opposite unit-amplitude e_y-polarized plane waves along +/-e_z, Eq. (1) | Same Eq. (1), local L2 distributional Maxwell model in Eqs. (3)-(4) | Same frequency, illumination and normalization |
| X_+=X_-=E_* exactly; 1-epsilon<Gamma<1, Eq. (4) | Same equalities/inequalities, Eq. (9) | No approximate target substituted |
| sup at fixed X=E_* of Gamma =1, and sup of absolute absorption difference =E_* | Identical suprema over explicit C_(k,P,Q,E_*), Eq. (10) | Same class and two sharp values |
| Lemma 1.2: X>0 implies Gamma<1 for each body | Lemma 4.2: X>0 implies 0<=Gamma<1; both suprema explicitly nonattained | Nonnegativity is made explicit; already follows from the absolute-value definition and positive denominator. Not a stronger physical claim |
| Gamma=absolute absorption difference/X=absolute scattering difference/X; X=A+S, Eq. (2) | Work, far field, energy balance and Gamma are separated into Eqs. (5)-(8) | Same area normalization and all-angle, both-polarization scattering |
| 'The pair (1)' interpreted as physical outgoing fields | Unique outgoing weak fields stated explicitly; a.e. uniqueness and canonical radiating representative explained | Clarification of the F2/F3 content already covered by the completed final audit |
| Every selected dimension/coefficient finite, no shared bounds on aperture/thickness/volume/resources or lower loss | Same limitations and explicit nonattainment | No fixed-resource, bandwidth or all-isotropic claim added |

The old and new strictness proofs use passivity, continuity of the far field and the forward optical theorem. The formal proof can instead use positive absorption at positive extinction. These are compatible routes to the same conclusion; identical proof presentation is not required by statement correspondence.

## Changes outside the main statement

The newer paper is a focused reorganization of the prescribed-extinction result. It makes the weak equations, radiation normalization, canonical representatives and scalar inverse argument explicit; presents the uniform aperture reasoning in a Weyl/Fourier organization; adds a geometry figure and expanded attribution; and separates the construction, aperture limit, exact tuning and positive-loss regularization into Sections 6-8. The formal localization proof has a different physical-space/L2 organization.

The October 11 specification's Section 6 contains distinct joint-resource and small-size variational/asymptotic results, and Section 7 numerical/algebraic diagnostics. These are not part of the audited Theorem 1.1/Lemma 1.2 and are not carried forward as formalized results of the focused publication paper. Causality/dispersion observations remain outside the main formal theorem. Removing those separate subjects is a scope change of the manuscript, not a weakening of its prescribed-extinction theorem.

The final audit's semantic PASS applies to the October 11 main theorem/lemma for the encoded two-layer class. This release's comparison transfers that main-statement correspondence to the newer paper. It does **not** certify every intermediate lemma, numerical constant, Weyl-fiber proof paragraph, appendix argument or expository presentation. S1 retains declaration-by-declaration distinctions among direct formal statements, consequences and differently organized proofs.

## Release changes

MANUSCRIPT_CHANGES.diff records every change from the newer publication baseline. Only formal-status paragraphs were edited: the final-commit audit is incorporated; audit positivity lemmas are acknowledged; historical pending-review metadata is contextualized; same-kernel replay and human peer review are distinguished. All scientific theorem, lemma, proposition, corollary and equation environments are unchanged. The build retained 51 numbered equations, 20 bibliography entries and the same geometry assets.
""")
put('AUDIT_PROVENANCE.md',f"""
# Completed audit provenance

## Exact final evidence

- Audited commit: `686402a6c2d63820828729cc7ab02504632e3fe7`.
- Audited tree: `580737ccf6557102d601894145cc0229ae1f83e3`.
- Declaration: `OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement`.
- Attached report: evidence/AUDIT_REPORT_686402a.md, SHA-256 `59a36c60a01d213c989ddf7547fbc63584770101b6eb5a6818bb3ad0d5f91eed`.
- Attached packet: evidence/oq7-final-audit-686402a.zip, SHA-256 `1e0c28039e81bcd9b5531a1e0d0e122190ef9780e9fec8d164467b5b1b032d30`.
- The report inside the packet is byte-identical to the standalone attachment.
- The report itself supplies no explicit audit date; this release does not invent one.

The final report records PASS for kernel validity, semantic fidelity to the October 11 Theorem 1.1/Lemma 1.2, Maxwell correctness within the formal model, both suprema/nonattainment, closure of F1-F4, and reproducibility with packaging defects R1/R2. These are completed existing audit results, not open proof obligations.

The accompanying audit programs, compressed build log and other logs are retained byte-for-byte under evidence/final/ and in the portable repository's audit/final/. A decompressed copy of build-all.log is provided in evidence/final/logs/ for convenience; the original .gz is preserved.

## Preceding audit recovered

evidence/preceding/AUDIT_REPORT_5a8350d.md has SHA-256 `{digest(preceding)}`. It is the preserved `verification/claude-independent-audit-5a8350d.md` from the frozen repository, examining commit `5a8350d5408c38e333c9f6b6d8a94816c794120b`, tree `a1b03d72e958851f2418f97a6b5c40c0689e305c`. Its kernel PASS and semantic/completeness FAIL described the existence-only stage; the final report closes those F1-F4 findings at the final commit. The regression program AuditExperiments.lean is also present in the final packet.

## Supplemental auditor theorems preserved

audit/final/experiments/Audit2.lean retains `auditor_extinction_pos`, `auditor_universal_gamma_lt_one`, `auditor_sup_is_lub` and the associated checks. The positive-extinction result rules out the formal division-by-zero branch for every admissible body/state. It remains accompanying audit evidence; it has not been silently inserted into or substituted for the frozen main theorem.

## Distinct kinds of evidence

| Evidence | What it establishes | Boundary |
|---|---|---|
| Lean kernel checking and standard-axiom census | Encoded theorem/proofs checked with Lean 4.34.1; only propext, Classical.choice, Quot.sound | Relative to that kernel/toolchain and definitions |
| Fresh replay independently run by the final auditor | PhysicalTheorem11 import closure replayed into an empty environment; reported exit 0, 10 min 45 s | Uses Lean's same kernel implementation; no independently implemented checker was used |
| AI-assisted semantic/model review | Reviewer's PASS correspondence and F1-F4 closure in the stated model | Distinct from human peer review and novelty |
| Current portable-release tests | Recorded commands/logs test the packaging revision and preserved audit programs | Not a newly commissioned generic audit |
| Human peer review | No completed human peer-review evidence supplied | Remains an external-review task |
| Scientific priority | Not established by any kernel or semantic verdict | Equation-level prior-art comparisons remain separate |

The final report's cone count is 61,839 constants; its whole-project sweep reports 5,658 project constants (49 private). The repository's historical count is 5,654. The report attributes this small difference to generated-declaration counting; both report the same three foundation axioms. Counts are not equated or used as a novelty measure.

## Historical metadata preserved

The immutable frozen manifest's export-time field says semantic review was not yet performed. It is retained as historical provenance and is superseded for current status by the attached completed final report. Likewise, earlier publication issue/provenance records remain unchanged in evidence/publication-baseline/. The release supplements now point to the final report and companion status record, rather than presenting those historical pending fields as current.

The corrected root was explicitly reauthorized by the user. The mistaken literal root was tested and returned PathNotFound. The two Downloads attachments were read by their explicitly supplied exact paths; Downloads was not searched. Originals and synced files were preserved. The earlier source inventory skipped both dependency junctions and recorded them; no external source link was followed.
""")
put('REPRODUCE.md',"""
# Reproduce the portable release

The immutable original is in frozen/OQ7-complete-physical-theorem11.bundle and its byte-preserved source ZIP. The separate portable revision is in portable-source.zip and portable-release.bundle. The main mathematical source files and all dependency revisions are unchanged.

## Tools and exact pins

Use Lean 4.34.1, compiler commit 5045d0056413266e57c625dcd7c365b10e377c52. Lake reports 5.0.0-src+5045d00 for that release. Use Git and Python 3.

Official release: https://github.com/leanprover/lean4/releases/tag/v4.34.1
Windows ZIP SHA-256: 457698d4e2132243e899ff32178d7ae63c16431d09ed9ad524d859c3581992af
Linux tar.zst SHA-256: 47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4

Compiler binaries are not duplicated in this source release. Install/activate the exact official release. The nine exact library source archives and their Git metadata are included in dependency-sources/, with all revisions in PINNED_DEPENDENCIES.json.

## Portable checkout

1. Verify SHA256SUMS from the release root.
2. Extract portable-source.zip into a directory called portable beside dependency-sources/. Keep the checkout path reasonably short on Windows.
3. Activate the pinned Lean bin directory in PATH; verify lean --version.
4. From portable/, run:

```text
python configure.py
python restore-dependencies.py --archives-directory ../dependency-sources
lake build OQ7 PrescribedExtinction
lake env lean verification/FinalCompleteTheorem.lean
python run-audit.py
```

restore-dependencies.py refuses to overwrite existing dependency directories, validates archive paths and requires each restored Git HEAD to equal its pinned revision. No dependency update is required. Alternatively, Lake may fetch the locked Git revisions online; do not run lake update.

The root lake-manifest.json is included and tracked. sources/pinned-lake-manifest.json remains a tracked recovery copy. Both use .lake/packages. configure.py and configure.ps1 restore the same relative configuration. Lake supplies the complete import environment; no manually assembled LEAN_PATH or absolute Windows dependency path is needed. The optional top-level env.sh/env.ps1 expose Lake wrappers after toolchain activation.

The original auditor's placeholder env.sh is preserved only under historical audit/final/ and evidence/final/. Do not source it; use the portable top-level wrapper or lake env.

Dependency compiled objects are not part of the archive. They can be rebuilt from included pinned sources; a compatible official Mathlib cache may accelerate this without changing pins. If using that cache, set MATHLIB_CACHE_DIR to a writable task-local directory before lake exe cache get.

## Existing audit programs

run-audit.py executes the byte-preserved Audit2.lean, AuditCone2.lean, AuditWholeProject.lean and AuditExperiments.lean through lake env. These include auditor_extinction_pos and related audit theorems. The final report and original logs are completed evidence even before a recipient reruns them.

Optional same-kernel fresh replay:

```text
lake env leanchecker --fresh --verbose PrescribedExtinction.PhysicalTheorem11
```

This repeats Lean's own kernel, not an independently implemented checker. The final auditor already reported a successful fresh replay. This release run does not claim a new independent kernel implementation.

## Manuscript

manuscript/main.tex and references.bib are the authoritative updated source; figure assets, build.py, template.html, PDF and offline MathML HTML are included. build.py uses Tectonic and Pandoc; provide their executable paths via --tectonic and --pandoc or put them in PATH. The current PDF was built with the previously available Tectonic 0.17.0 and Pandoc 3.12.1; the tools are not bundled.

Complete current test commands, exit codes, versions, warnings and output are in portable-test-logs/. The original audit log archives remain in evidence/final/logs/. PORTABLE_TEST_STATUS.json records the current test outcome and limits. POSIX execution was not tested on this Windows host; the configuration uses relative paths and standard Lake/Python commands.

Nothing in these instructions expands the result to fixed resources, bandwidth, arbitrary compact geometries or every interpretation of OQ7.
""")
put('PRIORITY_QUESTIONS.md',"""
# Remaining scientific-priority questions

Formal verification and the completed semantic audit do not establish priority. The release adds no new novelty verdict.

1. Compare Mann-Alu's 2023 maximal directional absorption contribution at equation level: what normalization, illumination pair, constitutive class and realizability assumptions does it use, and does it contain the combination of arbitrary fixed upper dielectric caps, compact local nonmagnetic two-layer bodies and every exact positive dimensional extinction target?
2. Complete equation-level comparison with reciprocal asymmetric-absorption metasurface work, including Yazdi et al. (2015) and Manez-Espina et al. (2026). Distinguish planar absorptance difference from the present compact extinction-normalized, all-angle scattering result; retain bianisotropy and resource assumptions.
3. Determine whether an earlier rigorous finite-aperture/localization theorem already supplies the specific uniform normalized limit at vanishing physical coupling needed for exact positive-extinction tuning under these material caps. Compare literal material truncation and computational/windowed Green-function methods with the same quantifiers.

These are focused questions preserved from the existing comparison materials; no new generic literature audit was commissioned. A qualified human Maxwell/model-correspondence review and any eventual journal peer review remain external-review tasks. No publication, submission or contact has been authorized or performed.
""")
status={'audited_commit':'686402a6c2d63820828729cc7ab02504632e3fe7','audited_tree':'580737ccf6557102d601894145cc0229ae1f83e3','declaration':'OQ7Prescribed.theorem11_complete','report_sha256':'59a36c60a01d213c989ddf7547fbc63584770101b6eb5a6818bb3ad0d5f91eed','verdicts':{'kernel':'PASS','semantic_fidelity_main_theorem':'PASS','Maxwell_correctness_within_model':'PASS','F1_F4':'CLOSED','suprema_nonattainment':'PASS'},'review_kind':'AI-assisted semantic/model review','fresh_replay':'Reported successful same-Lean-kernel fresh replay','independent_kernel_implementation_used':False,'human_peer_review_established':False,'novelty_established':False,'scope':'October 11 Theorem 1.1/Lemma 1.2, corresponding to newer Theorem 4.1/Lemma 4.2; not every intermediate statement'}
put('manuscript/reproducibility/final-audit-status.json',json.dumps(status,indent=2))
put('manuscript/reproducibility/AUDIT_PROVENANCE.md',(out/'AUDIT_PROVENANCE.md').read_text())
put('manuscript/reproducibility/MANUSCRIPT_VERSION_CORRESPONDENCE.md',(out/'MANUSCRIPT_VERSION_CORRESPONDENCE.md').read_text())
supp="""<!doctype html><html lang="en"><meta charset="utf-8"><title>OQ7 release supplements</title><style>body{max-width:58rem;margin:3rem auto;padding:0 1rem;font:17px/1.55 system-ui}table{border-collapse:collapse;width:100%}td,th{padding:.7rem;border:1px solid #bbb;text-align:left}code{overflow-wrap:anywhere}</style><h1>OQ7 release supplements</h1><p>Final audited commit: <code>686402a6c2d63820828729cc7ab02504632e3fe7</code>. The completed AI-assisted final audit reports kernel and semantic PASS and closure of F1-F4.</p><table><tr><th>Supplement</th><th>Contents</th></tr><tr><td>S1</td><td><a href="../theorem-correspondence.html">Theorem correspondence</a> and <a href="MANUSCRIPT_VERSION_CORRESPONDENCE.md">manuscript version comparison</a>. Main theorem correspondence does not certify every intermediate proof presentation.</td></tr><tr><td>S2</td><td><a href="OQ7-complete-physical-theorem11-source.zip">Immutable frozen source</a> and <a href="OQ7-complete-physical-theorem11.bundle">Git history</a>. The outer release also supplies a separate portable revision and all pinned dependency sources.</td></tr><tr><td>S3</td><td><a href="manifest.json">Original frozen verification manifest</a> and <a href="final-audit-status.json">completed final-audit status</a>. Original pending-review metadata is historical. <a href="AUDIT_REPORT_686402a.md">Final audit report</a>; its exact programs/logs are in the outer evidence packet and portable repository.</td></tr><tr><td>S4</td><td><a href="AUDIT_PROVENANCE.md">Audit provenance</a>. Preceding audit and auditor_extinction_pos are preserved. Same-kernel replay, AI-assisted review and human peer review are distinct.</td></tr></table><p>Human peer review and scientific priority are not established by these materials. The theorem is single-frequency and resource-unrestricted in the stated two-layer class; no bandwidth, fixed-resource or all-OQ7 claim is made.</p><p><a href="../paper.pdf">Updated manuscript PDF</a> · <a href="../paper.html">Offline HTML</a> · <a href="../main.tex">LaTeX source</a></p></html>"""
put('manuscript/reproducibility/SUPPLEMENT_INDEX.html',supp)
# Machine-readable S1 data gains a sidecar; original correspondence scientific rows stay byte-preserved.
put('manuscript/reproducibility/CORRESPONDENCE_AUDIT_SCOPE.md','The completed final-commit audit validates the main theorem/lemma correspondence. The S1 table is a source/declaration map, not a claim that the auditor certified every intermediate statement or every expository proof paragraph. See MANUSCRIPT_VERSION_CORRESPONDENCE.md and AUDIT_PROVENANCE.md.')
put('RELEASE_INDEX.md',"""
# OQ7 prescribed-extinction release

The completed final audit of commit 686402a6c2d63820828729cc7ab02504632e3fe7 reports PASS for kernel checking, main-theorem semantic fidelity and F1-F4 closure. This release incorporates that existing evidence, preserves all originals and supplies a separate portable packaging revision. It is a local release package; nothing was published, submitted or sent.

| Location | Purpose |
|---|---|
| frozen/ | Exact audited source ZIP, complete original Git bundle and historical verification manifest |
| evidence/AUDIT_REPORT_686402a.md and evidence/oq7-final-audit-686402a.zip | Byte-preserved final report and audit packet |
| evidence/final/ | Extracted audit programs and logs, plus readable decompressed build log |
| evidence/preceding/ | Recovered preceding audit of 5a8350d |
| evidence/manuscripts/ and evidence/publication-baseline/ | Preserved October 11 scientific specification and newer publication baseline |
| dependency-sources/ | All nine exact pinned dependency source snapshots, Git metadata snapshots and pin manifest |
| portable-source.zip and portable-release.bundle | Separate portable release revision; mathematical sources unchanged |
| manuscript/ | Updated LaTeX source, bibliography, assets, 16-page PDF, offline HTML and updated S1-S4 supplements |
| MANUSCRIPT_VERSION_CORRESPONDENCE.md | Precise Theorem 1.1/Lemma 1.2 to Theorem 4.1/Lemma 4.2 comparison and scope limits |
| AUDIT_PROVENANCE.md | Final/preceding review identities and distinctions among kernel, replay, semantic and human review |
| REPRODUCE.md | Portable locked-dependency build and audit-program instructions |
| RELEASE_DIFFERENCES.md and PORTABLE_TEST_STATUS.json | Exact packaging changes, mathematical-source preservation and current tests |
| portable-test-logs/ | Complete commands, exit codes, versions, warnings and output from this run |
| PRIORITY_QUESTIONS.md | Short list of unresolved equation-level priority comparisons |
| SHA256SUMS | Content checksums for every release file except the checksum manifest itself |

The complete source-and-audit archive is supplied beside this directory. SHA256SUMS uses relative paths from the release root. The separate archive checksum is supplied beside the archive to avoid a self-referential checksum.

## Completed proof/audit work

The frozen main theorem and its semantic/model audit are completed evidence. Both suprema and nonattainment, arbitrary-state well-posedness/optics/reciprocity and F1-F4 are covered within the formal two-layer model. auditor_extinction_pos and related auditor lemmas are preserved as separate evidence. The final report records successful fresh replay using the same Lean kernel; no independently implemented checker is claimed.

## Release work and remaining tasks

The current release adds portable configuration, a tracked root manifest, dependency snapshots, completed-audit supplements, manuscript-status revisions, exact differences and recorded tests. The audit does not establish human peer review, scientific priority, finite bandwidth, fixed-resource performance or every interpretation of OQ7. Those are external or separately scoped questions, not pending repetitions of the completed final audit.
""")
print('RELEASE_DOCUMENTS_AND_COMPLETED_AUDIT_SUPPLEMENTS_WRITTEN')
