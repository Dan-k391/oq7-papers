"""Export a qualified publication-to-frozen-Lean correspondence table."""
from pathlib import Path
import csv
import hashlib
import html
import json
import re
import shutil
import subprocess
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent / "oq7-prescribed-extinction"
aux = (ROOT / "build/main.aux").read_text(encoding="utf-8")
labels = dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}", aux))
declarations = {}
for entry in json.loads((ROOT / "review/lean-source-inventory.json").read_text(encoding="utf-8")):
    p = REPO / entry["file"]
    for m in re.finditer(r"^(?:theorem|def|structure|abbrev)\s+(\S+)", p.read_text(encoding="utf-8-sig"), re.M):
        name = m.group(1)
        declarations.setdefault(name, []).append((entry["file"], p.read_text(encoding="utf-8-sig")[:m.start()].count("\n") + 1))

rows = [
 ("thm:main", "Main complete theorem", "theorem11_complete", "Direct complete statement", "Existence plus all-class well-posedness, optics, reciprocity, strictness, and both exact suprema. k>0, P>1, Q>0, E_*>0; epsilon in (0,1); same two-layer local nonmagnetic class."),
 ("eq:main", "Exact prescribed-extinction witness", "theorem11", "Direct existence core", "Both extinctions equal the positive target exactly, and 1-epsilon<Gamma<1. Weak fields are existentially supplied; uniqueness comes from the complete theorem."),
 ("eq:suprema", "Normalized supremum", "prescribedExtinctionAsymmetryValues_sSup", "Direct all-class supremum", "The set is the range over every PrescribedExtinctionPair, not only the constructed family; nonempty and IsLUB proofs precede sSup."),
 ("eq:suprema", "Unnormalized supremum", "prescribedExtinctionDifferenceValues_sSup", "Direct all-class supremum", "The supremum of the dimensional absolute absorption difference is the prescribed target."),
 ("lem:strict", "Universal strict nonattainment", "universal_physical_asymmetry_lt_one", "Direct conclusion; alternative proof", "Lean uses strictly positive absorption within the admissible class. Prose uses positive-extinction scattering strictness via far-field continuity/optical theorem."),
 ("lem:strict", "Zero scattering forces zero extinction", "physicalScattering_zero_extinction", "Direct optical strictness lemma", "The far field of a locally L2 compact current is continuous; exact current and physical flux interpretations are supplied separately."),
 ("eq:material", "Material bounds", "MaterialAdmissible", "Direct definition", "Transpose reciprocity; quadratic-form real bounds I to PI; strictly positive imaginary form on every nonzero complex vector; upper loss QI."),
 ("sec:model", "Finite geometry", "TwoLayerBody", "Direct definition", "Positive finite square side R and thicknesses h,d. Open material domain and compact closure differ only on a null boundary."),
 ("eq:maxwell", "Weak Maxwell equations", "WeakMaxwell", "Direct definition", "Locally L2 actual electric and impedance-normalized magnetic fields; distributional curls against every smooth compact complex vector test. mu=I is built in."),
 ("eq:outgoing", "Radiation condition", "Outgoing", "Direct definition", "Uniform Silver-Muller residual over all exterior points, not a specular/channel condition. A canonical exterior representative carries physical pointwise flux."),
 ("eq:incident", "Incident pair", "incidentElectric;incidentMagnetic", "Direct definitions", "Electric basis index 1 is e_y; propagation axis index 2 is e_z. Minus magnetic field has the time-reversal sign. Electric amplitude one."),
 ("eq:work", "Power work definitions", "extinction;absorption", "Direct definitions", "Extinction is k Im integral of conjugate incident field times polarization; absorption is local tensor dissipation. Both have units of area."),
 ("eq:farfield", "All-angle scattering", "currentFarField;scattering", "Direct definitions plus physical certificate", "Original spherical-coordinate integral includes both vector polarizations. It is identified with sphere-area integral and actual outgoing flux by the completed optics theorem."),
 ("prop:physical", "Well-posedness almost everywhere", "physicalScatteringState_wellposed_ae", "Direct universal statement", "For every admissible two-layer body and direction, all original weak states have electric and magnetic fields equal almost everywhere."),
 ("prop:physical", "Converse volume representation", "scatteringState_converse_material_volume_equation", "Direct universal representation", "An arbitrary original scattering state satisfies the actual constitutive volume equation; this is not assumed as a structure field."),
 ("eq:balance", "Energy balance", "scatteringState_energy_balance", "Direct universal identity", "Original X=A+S for every original weak state, using its body volume representation."),
 ("eq:balance", "Opposite-incidence reciprocal extinction", "admissibleScatteringState_extinction_reciprocity", "Direct identity", "No common-extinction identity is assumed as a hypothesis; reciprocal tensors and actual states imply it."),
 ("eq:balance", "Forward optical theorem", "scatteringState_forward_optical_theorem", "Direct identity", "Physical normalization 4*pi/k and original e_y forward component match the paper."),
 ("eq:farfield", "Canonical radiation and physical sphere flux", "scatteringState_full_optical_theorem", "Direct aggregate certificate", "AE representatives, full sphere-area scattering identity, sphere-flux limit, and uniform actual electric far-field amplitude with quantitative error."),
 ("eq:gamma", "Absorption/scattering asymmetry equality", "universal_physical_asymmetry_eq_scattering_difference", "Direct identity", "Follows for arbitrary admissible opposite states from reciprocal extinction and both energy balances."),
 ("eq:radiation", "Outgoing radiation work", "physicalOutgoingVolume_farField_work", "Equivalent physical operator identity", "The L2 compact-current work equals the full spherical radiation quadratic form. Lean uses its actual volume operator and sphere-area measure."),
 ("eq:green-bound", "Bounded Green operator and displayed volume bound", "compactStaticOperator_apply_norm_le;compactOutgoingOperator_norm_le", "Related boundedness statements; numerical volume bound not separately matched", "The static norm bound and finite-radius outgoing boundedness are formal. The specific 3/4*k^2*(3|D|/(4*pi))^(2/3) estimate is retained from primary PDF Eq. (8), with its ordinary Schur proof; do not claim an identical Lean declaration."),
 ("eq:scalar-inverse", "Aperture/angle-independent scalar inverse", "activeMaterialEquiv_inverse_norm_le", "Direct inverse bound with sign translation", "Lean's activeMaterialOperator is the negative of the manuscript L operator and solves the negative drive. Inverse norm and physical response are identical. c0=min(Im alpha/|alpha|^2,Im beta/|beta|^2)."),
 ("eq:normalized", "Exact physical current sine factorization", "activePhysicalSolution_sine_factorization", "Direct factorization", "The normalized response is defined at theta=0; it is not a positive-extinction zero-angle physical field."),
 ("eq:factorization", "Extinction sine-square factorization", "physicalExtinction_sine_squared_factorization", "Direct factorization", "Actual current/field and original dimensional work normalization."),
 ("eq:factorization", "Absorption sine-square factorization", "physicalAbsorption_sine_squared_factorization", "Direct factorization", "Actual tensor absorption equals the normalized scalar-current quadratic form."),
 ("eq:factorization", "All-angle scattering sine-square factorization", "physicalScattering_sine_squared_factorization", "Direct factorization", "The original full spherical scattering integral factors exactly; no channels are dropped."),
 ("eq:aux-ratio", "Ratio after cancellation", "physicalAsymmetry_normalized_factorization", "Direct identity", "Requires sin(theta) nonzero for the physical ratio; auxiliary normalized ratio remains defined at zero."),
 ("eq:plate-design", "Plate for every cap P>1", "exists_plateDesign_within_cap;plateDesign_phases", "Direct design statements", "Integer j, real cap, finite positive plate width, even/odd principal-axis phases."),
 ("eq:jones", "Exact lossless plate transmission", "losslessPlateDesign_actual_coefficients", "Direct scalar coefficients; Cartesian construction", "Boundary transmission one along active axis, vacuum phase minus one, zero reflection. Jones form follows in real orthogonal principal axes."),
 ("eq:absorber", "Nearly perfect finite absorber with arbitrarily small allowed loss", "exists_nearlyPerfect_absorber_with_loss_cap", "Direct existence statement", "The scalar transfer coefficients and thick-limit proof supply finite h and eta under any Q>0. The explicit eta=1/N,kh=N^2 sequence is the ordinary source exposition."),
 ("eq:lossless-planar", "Normalized lossless planar powers", "losslessPlateDesign_coupled_power_values", "Direct zero-angle values; general-angle prose identity", "Lean declaration gives auxiliary theta=0 values B+=0, B-=4Ax, Y=4. Arbitrary-angle sin/cos formula is supplied by exact source amplitude matching; do not label it the literal statement of this declaration."),
 ("eq:planar-continuity", "Joint positive-loss/angle continuity at zero", "slabDesignAsymmetry_joint_continuousAt_zero", "Direct joint ratio continuity", "The actual slab/current identification is planarNormalizedAsymmetry_eq_slabFormula. No division of vanishing physical powers is used."),
 ("lem:planar", "Planar design within caps, near-unit normalized zero-angle ratio", "exists_planar_design_near_unit_asymmetry", "Direct existence statement", "Real eigenvalues within P, positive active losses less than Q/3, finite positive widths, and the desired zero-angle auxiliary asymmetry."),
 ("eq:aperture-current", "Uniform normalized current aperture limit", "physicalBody_normalized_response_uniform_aperture_localization", "Direct epsilon-form convergence", "Formal radius threshold is uniform over all real angles (stronger than compact interval restriction), at fixed k,h,d,alpha,beta with positive active imaginary parts."),
 ("eq:aperture-power", "Uniform normalized work/absorption limits", "physicalBody_normalized_powers_uniform_aperture_localization", "Direct epsilon-form power convergence", "Radius threshold independent of angle; error <=epsilon*R^2 in the auxiliary normalized powers."),
 ("eq:aperture-power", "Uniform original physical all-angle power approximation", "physicalRankOne_original_powers_uniform_aperture_localization", "Direct original-power convergence", "Combined X,A,S error <=epsilon*R^2*sin(theta)^2, including theta=0 without division."),
 ("thm:aperture", "Uniform ratio including shrinking angles", "physicalBody_normalized_asymmetry_uniform_aperture_localization", "Direct compact-set ratio limit", "Compact angle set, positive planar extinction lower bound, and the normalized ratio. Original ratio version separately assumes sin(theta) nonzero."),
 ("eq:weyl-blocks", "Weyl fibers and mixed Fourier proof organization", "", "Ordinary Fourier exposition; different Lean localization route", "The manuscript supplies the Weyl derivation. Lean proves the physical aperture result through physical-space, smooth-slab and height-L2 estimates, not a separately exported identical Weyl-fiber lemma."),
 ("eq:commutator", "Global auxiliary Fourier identity before aperture restriction", "", "Ordinary corrected exposition; not an identical Lean declaration", "Eq. (35) transforms the global H-tilde on the transverse strip. Its restriction H on D_R is estimated through low-frequency global L2 and high-frequency global transverse Linfinity bounds; no global L2 estimate across grazing is asserted."),
 ("eq:current-error", "Smooth-window residual and current comparison", "physicalBody_uniform_sharp_response_estimate", "Equivalent physical residual estimate", "The same fixed-window-then-aperture-then-density logic is formalized; no aperture-uniform Green norm or uniform vanishing-loss estimate is claimed."),
 ("eq:angle-bracket", "First exact extinction bracket", "physicalRankOne_exists_extinction_bracket", "Equivalent exact bracket construction", "Lean's quantified bracket does not require the manuscript's explicit inverse-R endpoint formula; both establish finite strict endpoint inequalities and a compact interval near zero."),
 ("eq:endpoints", "First finite rank-one exact target root", "physicalRankOne_prescribedExtinctionOfPlanarDesign", "Direct exact root existence", "Physical original extinction equals the positive target and ratio exceeds the chosen planar lower threshold. Monotonicity is not assumed."),
 ("eq:root-scaling", "Inverse-aperture angle scaling for rank-one roots", "", "Ordinary source corollary; not separately matched", "Primary Eq. (36) follows from uniform localization and sin(theta)/theta->1. Not asserted as an identically phrased Lean declaration or a final-loss resource rate."),
 ("eq:electric-inverse", "Full-vector inverse at zero isotropic loss", "woodburyElectricOperator_right_inverse;woodburyElectricOperator_left_inverse", "Direct bounded operator identity with model translation", "PhysicalElectricWoodbury builds rankOneElectricUnit for the actual body. The operator ordering is preserved."),
 ("eq:positive-loss", "Preserving the compact bracket under positive isotropic loss", "physicalPerturbed_preserves_compact_bracket", "Direct uniform continuity/bracket statement", "Fixed finite body; positive small nu below the chosen cap; strict endpoints and ratio floor preserved over compact angle set."),
 ("sec:realization", "Second exact extinction tuning", "physicalIsotropic_prescribedExtinctionOfPlanarDesign", "Direct final witness", "Positive nu, retuned finite angle, both exact target extinctions, ratio lower threshold and strict upper bound; actual perturbed volume solutions."),
 ("eq:positive-loss", "Final material admissibility", "isotropicRankOneBody_admissible", "Direct cap/loss verification", "Same transpose reciprocity and real/loss quadratic bounds in both layers; positive isotropic loss restores null-direction loss."),
 ("eq:deficit", "Limiting allocation of absorption and scattering", "", "Algebraic consequence of certified identities", "Energy balance and nonnegative powers imply the stated limiting powers as Gamma->1 at fixed positive target; no separate named Lean limit theorem claimed."),
 ("eq:directivity", "Forward directivity obstruction", "", "Ordinary optical-theorem consequence and prior art", "Retained from supporting paper Eq. (5); not claimed as a new discovery or separately formalized declaration."),
 ("eq:lorentz", "Passive causal oscillator compatibility at one frequency", "", "Ordinary source observation outside formal main theorem", "Primary Section 5.3; does not impose a bandwidth model in Lean or prove finite-bandwidth performance."),
 ("app:weak", "Entire outgoing weak vacuum uniqueness", "vacuum_outgoing_weak_unique_zero", "Direct weak uniqueness conclusion", "Weighted Poynting/Lorentz and smooth-current testing; equality is almost everywhere. The prose reorganizes those underlying arguments."),
 ("app:amplitudes", "Nonsingular planar amplitude vectors", "", "Source-derived appendix; normalized slab result formally identified", "Primary Appendix A supplies the displayed four-component amplitudes. Actual normalized absorption/extinction and zero-angle joint limit have direct Lean declarations; no exact vector-form declaration is asserted."),
]

result=[]
for label, statement, names, relationship, notes in rows:
    locations=[]
    for name in names.split(";") if names else []:
        if name not in declarations:
            raise RuntimeError(f"Unverified declaration name: {name}")
        locations.extend(f"{p}:{line}" for p,line in declarations[name])
    result.append(dict(manuscript_label=label,manuscript_number=labels.get(label,""),statement=statement,
                       lean_declarations="; ".join("OQ7Prescribed."+n for n in names.split(";") if n),
                       frozen_source_locations="; ".join(locations),relationship=relationship,assumptions_and_scope=notes))
with (ROOT/"theorem-correspondence.csv").open("w",encoding="utf-8-sig",newline="") as f:
    w=csv.DictWriter(f,fieldnames=list(result[0]));w.writeheader();w.writerows(result)
header="<tr>"+"".join("<th>"+html.escape(k.replace("_"," ").title())+"</th>" for k in result[0])+"</tr>"
body=[]
for row in result:
    cells=[]
    for k,v in row.items():
        if k=="manuscript_label":
            cells.append('<td><a href="paper.html#'+html.escape(v)+'">'+html.escape(v)+'</a></td>')
        else:
            cells.append("<td>"+html.escape(v)+"</td>")
    body.append("<tr>"+"".join(cells)+"</tr>")
(ROOT/"theorem-correspondence.html").write_text('<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>OQ7 theorem correspondence</title><style>body{font:16px/1.5 system-ui;margin:24px;color:#213547}table{border-collapse:collapse;min-width:1250px}th,td{border:1px solid #ccd7e0;padding:12px;vertical-align:top}th{background:#eaf0f4;text-align:left}tbody tr:nth-child(even){background:#f7f9fb}.scroll{overflow:auto}a{color:#1f5681}</style><h1>OQ7 Paper 1: theorem correspondence</h1><p>Frozen commit: 686402a6c2d63820828729cc7ab02504632e3fe7. Direct declarations, equivalent formulations, and ordinary auxiliary exposition are distinguished. The frozen manifest records independent semantic review as pending at export; <a href="reproducibility/AUDIT_PROVENANCE.md">Supplement S4</a> identifies the currently available audit evidence.</p><div class="scroll"><table><thead>'+header+'</thead><tbody>'+"\n".join(body)+'</tbody></table></div></html>',encoding="utf-8")

# Current machine checks for every named correspondence entry, using the frozen aggregate.
names=sorted({name for row in rows for name in row[2].split(";") if name})
(ROOT/"review/CorrespondenceCheck.lean").write_text("import PrescribedExtinction.PhysicalTheorem11\n\n"+"\n".join("#check OQ7Prescribed."+n for n in names)+"\n",encoding="utf-8")

inputs=[]
for name,role in [
    ("OQ7_prescribed_extinction_2026-10-11.pdf","Primary: prescribed-extinction portions"),
    ("OQ7_compact_Maxwell_cross_sections_2026-10-10.pdf","Supporting: analytic foundations"),
    ("OQ7_quartic_Maxwell_2026-10-10.pdf","Reference only; separate quartic project"),
    ("OQ7_quartic_adversarial_audit_2026-10-10.pdf","Reference-only audit"),
    ("OQ7_fixed_resource_bounds_2026-10-10.pdf","Reference only; fixed resources"),
    ("OQ7_generalized_research_2026-10-10.pdf","Reference only; scalar/channel context")]:
    p=Path(r"C:\Users\Daniel\Downloads")/name
    inputs.append(dict(path=str(p),name=name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),pages=len(PdfReader(p).pages),role=role))
for p in [REPO/"verification/claude-independent-audit-5a8350d.md",ROOT.parent/"oq7-mission/NOVELTY_REVIEW.md",ROOT.parent/"oq7-mission/MAXWELL_LOCALIZATION_AUDIT.md",ROOT.parent/"oq7-mission/MATHEMATICAL_AUDIT.md",ROOT.parent/"oq7-mission/MANUSCRIPT_STATUS_ADDENDUM.md"]:
    inputs.append(dict(path=str(p),name=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),role="Historical reference report; applies to stated version/commit"))
(ROOT/"review/input-manifest.json").write_text(json.dumps(inputs,indent=2),encoding="utf-8")

frozen=ROOT.parent/"oq7-physical-theorem11-review-686402a6c2d6"
dest=ROOT/"reproducibility"
dest.mkdir(exist_ok=True)
copied=[]
for name in ["OQ7-complete-physical-theorem11-source.zip","OQ7-complete-physical-theorem11.bundle","manifest.json","INDEPENDENT_REVIEW_PROMPT.md"]:
    original=frozen/name
    shutil.copyfile(original,dest/name)
    before=hashlib.sha256(original.read_bytes()).hexdigest()
    assert before==hashlib.sha256((dest/name).read_bytes()).hexdigest()
    copied.append(dict(name=name,sha256=before,original=str(original)))
(dest/"copy-manifest.json").write_text(json.dumps(copied,indent=2),encoding="utf-8")
print(f"Exported {len(result)} qualified correspondence rows and {len(names)} current declaration checks; copied frozen artifacts byte-for-byte.")
