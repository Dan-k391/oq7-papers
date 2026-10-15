# Literal numbered-statement scope review

This is an **AI-assisted source/type correspondence review**, not human peer review or an independently implemented kernel check. It audits the preserved original dated statements, including clauses before their Proof markers. It does not replace the source-bound combined replay records.

## Current release gate

All 23 original numbered statements have matching complete interfaces in the final source-bound replay: 15 generalized statements and eight quartic statements. The audit found two omitted within-statement clauses before the final freeze. Both are now included: Proposition 2.1 prescribed-entry phase and zero-product cases, and Theorem 6.3 complete Eq52 equality family. The final reports and exact source hashes are recorded in the JSON companion.

The JSON companion records the original PDF/TXT and reading-TeX hashes, exact roots, source-file hashes, all active current proof-source hashes and unchanged baseline dependency hashes. No historical audit is overwritten.

## Statement clauses and interfaces

### generalized-research — Proposition 2.1

Status: `complete-source-and-final-replay-correspondence`.

- Actual reciprocal complex two-port realizability iff all magnitude conditions and F(|delta|)>=0.
- Every valid pair T,a is realizable, including endpoints.
- Prescribed nonzero entries: exact cosine of arg(rL)+arg(rR)-2arg(t) criterion.
- Zero-product case T*|rL*rR|=0: no phase quotient; the remaining determinant inequality is necessary and sufficient.

Exact interfaces: `GeneralizedResearch.ScalarBenchmark.feasibility_iff`, `GeneralizedResearch.ScalarBenchmark.zero_feasible`, `GeneralizedResearch.ScalarPhaseFeasibility.proposition21`, `GeneralizedResearch.ScalarPhaseFeasibility.prescribed_entry_phase_iff`, `GeneralizedResearch.ScalarPhaseFeasibility.degenerate_entry_iff`.

The independent audit found these original within-statement clauses and the final ScalarPhaseFeasibility module closes them with actual complex passive matrices; no phase conclusion is assumed as a premise.

### generalized-research — Proposition 2.2

Status: `complete-source-and-final-replay-correspondence`.

- Exact attained maximum for every feasible T,a, with both active and plateau branches.
- The branches agree at the interface and include T=0 and T=1.

Exact interfaces: `GeneralizedResearch.ScalarBenchmark.sharp_ceiling`, `GeneralizedResearch.ScalarBenchmark.optimizer_attains`, `GeneralizedResearch.ScalarBenchmark.ceiling_active`, `GeneralizedResearch.ScalarBenchmark.ceiling_plateau`, `GeneralizedResearch.ScalarBenchmark.ceiling_transition`, `GeneralizedResearch.ScalarBenchmark.ceiling_at_unit_transmission`.

The separate full optimizer/singular-spectrum classification follows the Proof under an unnumbered heading. It is outside this numbered statement and must retain its separate ledger status.

### generalized-research — Lemma 4.1

Status: `complete-source-and-final-replay-correspondence`.

- Actual fundamental Helmholtz solution modulus comparison on every selected interval, including h=0 and h=pi/K.

Exact interfaces: `GeneralizedResearch.HelmholtzProfile.Profile.modulus_comparison`, `GeneralizedResearch.HelmholtzProfile.Profile.cell_comparison`.

The broad profile model does not impose a positive lower bound on the real coefficient p; fields, derivatives, passivity and local integrability are explicit model hypotheses.

### generalized-research — Lemma 4.2

Status: `complete-source-and-final-replay-correspondence`.

- Exact capped Fourier moment inequality for every nonnegative measurable capped loss on a cell of length at most pi/K.

Exact interfaces: `OQ7.capped_fourier_moment_Ioo`.

Open interval endpoints do not change Lebesgue mass or Fourier integral. This is an unchanged preserved-library result.

### generalized-research — Lemma 4.3

Status: `complete-source-and-final-replay-correspondence`.

- Cell parameter u=K*m/Q lies in [0,pi].
- Actual unit-incidence absorption determinant divided by actual transmission is at least (Q/P)^2*f(u).
- Any finite family of disjoint such cells gives sqrt(c)>=(Q/P)*sum(g(u)).

Exact interfaces: `GeneralizedResearch.HelmholtzProfile.Profile.lemma43_parameter_range`, `GeneralizedResearch.HelmholtzProfile.Profile.unitCellGram_normalized_det`, `GeneralizedResearch.HelmholtzProfile.Profile.lemma43_cell`, `GeneralizedResearch.HelmholtzProfile.Profile.lemma43`, `GeneralizedResearch.HelmholtzProfile.Profile.disjoint_cell_rest_posSemidef`, `GeneralizedResearch.HelmholtzProfile.Profile.disjoint_resource_cells`.

The final 71-module development added the literal unit-incidence transfer/congruence and actual disjoint-cell aggregation. A generic PSD Gram inequality alone would not cover this statement.

### generalized-research — Lemma 4.4

Status: `complete-source-and-final-replay-correspondence`.

- g is convex on [0,pi/2].
- Every tangent at 0<x<=1/3 lies below g throughout [0,pi].

Exact interfaces: `OQ7.ResourceScalar.g_convex_half`, `OQ7.ResourceScalar.g_tangent_full`.

### generalized-research — Theorem 4.5

Status: `complete-source-and-final-replay-correspondence`.

- Finite half-cell resource floor beta_nh and its explicitly positive rational lower bound.
- Full-cell improvement under either U<=pi/2 or U/nf<=1/3.
- The full-cell condition holds eventually as L increases.
- Uniform inverse-square lower asymptotic, including every sequence of varying admissible profiles.

Exact interfaces: `GeneralizedResearch.HelmholtzProfile.Profile.theorem45_finite`, `GeneralizedResearch.HelmholtzProfile.Profile.full_floor_eventually`, `GeneralizedResearch.HelmholtzProfile.Profile.theorem45_uniform_asymptotic`, `GeneralizedResearch.HelmholtzProfile.Profile.theorem45_sequence_lowerlimit`.

Strict nonattainment of these finite-cell floor inequalities is the separately numbered Remark 4.6, not a clause of this theorem; its open status must not be confused with Theorem 5.1 finite-stack strictness.

### generalized-research — Theorem 5.1

Status: `complete-source-and-final-replay-correspondence`.

- Every sufficiently large thickness budget has a nonempty exact T,a,M finite-layer class.
- The actual class supremum has the precise inverse-square asymptotic constant.
- Every finite admissible exact-target stack has asymmetry strictly below D0.
- The matching sequence consists of ordinary bounded dielectric layers with exact target values.

Exact interfaces: `GeneralizedResearch.sharp_exact_target_thickness`, `GeneralizedResearch.admissible_layer_helmholtz`, `GeneralizedResearch.exact_target_field_continuous`.

The wrapper imports unchanged OQ7.theorem51. Its displayed conjunction explicitly includes strict finite-stack D<D0; no matching sequence is assumed as a premise.

### generalized-research — Corollary 5.2

Status: `complete-source-and-final-replay-correspondence`.

- Actual infimum of finite-layer near-optimal thickness has the precise eta^(-1/2) asymptotic and original leading constant.

Exact interfaces: `GeneralizedResearch.corollary52`, `GeneralizedResearch.corollary52_original_ratio`, `GeneralizedResearch.nearOptimalThicknesses_nonempty`, `GeneralizedResearch.minimumThickness_tendsto_atTop`.

The proof constructs and compares actual near-optimal layer-budget sets. It does not assert the infimum is attained.

### generalized-research — Proposition 6.1

Status: `complete-source-and-final-replay-correspondence`.

- Exact common extinction for a unit input and its lossless-reference time reverse.
- Signed absorption difference is minus the signed scattering difference.

Exact interfaces: `GeneralizedResearch.hilbert_extinction_reciprocity`, `GeneralizedResearch.ChannelEquality.reciprocal_power_difference`.

### generalized-research — Theorem 6.2

Status: `complete-source-and-final-replay-correspondence`.

- Extinction lies in [0,4]; absolute absorption and scattering differences agree and are at most X-X^2/4.
- Every X in the closed interval is attained by an actual reciprocal passive three-port with orthogonal reversed inputs.
- Interior equality iff, after swapping inputs, S*u=(1-X/2)*S0*u and the other output has unit norm.
- At X=0 and X=4 both inputs are mapped to the corresponding plus/minus background outputs and both absorptions vanish.

Exact interfaces: `GeneralizedResearch.hilbert_reciprocal_absorption_parabola`, `GeneralizedResearch.ChannelParabola.theorem62`, `GeneralizedResearch.ChannelParabola.sharpness`, `GeneralizedResearch.ChannelEquality.reversed_scattering_difference_abs`, `GeneralizedResearch.ChannelEquality.reversed_equality_iff`, `GeneralizedResearch.ChannelEquality.reversed_endpoint_zero`, `GeneralizedResearch.ChannelEquality.reversed_endpoint_four`.

Sharpness is transported from the literal finite matrix to the same Hilbert model as the upper bound; it is not only an SDP relaxation.

### generalized-research — Theorem 6.3

Status: `complete-source-and-final-replay-correspondence`.

- Universal free-extinction scalar two-port ratio is at most sqrt(10*sqrt(5)-22).
- All equality matrices, up to swapping ports, are exactly Eq52 for every real phase phi; conversely the entire family is passive and attains equality.

Exact interfaces: `GeneralizedResearch.GoldenClassification.theorem63`, `GeneralizedResearch.GoldenClassification.equality_family_iff`, `GeneralizedResearch.GoldenClassification.family_attains`.

The independent audit identified Eq52 as part of the numbered statement. The final combined proof now includes the full iff classification, every real phase and port swap, in addition to the universal bound; the earlier single-witness theorem alone was insufficient.

### generalized-research — Theorem 6.4

Status: `complete-source-and-final-replay-correspondence`.

- For every k>0, -1<t<1, eta>0 and h>0 there is the stated actual two homogeneous nonmagnetic anisotropic dielectric layer construction with identical vacuum exteriors.
- AL=0, AR=(1-t^2)*Ax>0 and exact common extinction 2(1-t).
- Real permittivity eigenvalues lie in [1,4]; loss is PSD and has the specified nonzero first-layer eigenvalue eta; coefficients and widths are finite.
- The actual sequence eta_m=1/m, k*h_m=m^2 has Ax tending to one.
- Every prescribed interior extinction has exact parabolic supremum in this physical planar class; free-extinction relative supremum is one.

Exact interfaces: `GeneralizedResearch.PlanarRealization.interface_continuity`, `GeneralizedResearch.PlanarRealization.left_boundary`, `GeneralizedResearch.PlanarRealization.right_boundary`, `GeneralizedResearch.PlanarRealization.absorber_constitutive`, `GeneralizedResearch.PlanarRealization.reference_vacuum`, `GeneralizedResearch.PlanarRealization.response_passive`, `GeneralizedResearch.PlanarRealization.physical_power_values`, `GeneralizedResearch.PlanarRealization.physical_extinction_values`, `GeneralizedResearch.PlanarPlateBridge.tensor3_spectral_decomposition`, `GeneralizedResearch.PlanarPlateBridge.tensor3_bounds_j1`, `GeneralizedResearch.PlanarPlateBridge.constitutive_current3`, `GeneralizedResearch.PlanarSharpness.difference_strict_bounds`, `GeneralizedResearch.PlanarSharpness.difference_tendsto`, `GeneralizedResearch.PlanarSharpness.fixed_extinction_supremum`, `GeneralizedResearch.PlanarSharpness.relative_supremum`.

The laterally infinite geometry and actual layer fields are retained. The natural-number sequence uses m+1 to avoid zero; this is the same positive-integer sequence after reindexing.

### generalized-research — Corollary 6.5

Status: `complete-source-and-final-replay-correspondence`.

- For every interior extinction, actual laterally infinite stacks admit unit-power finite transverse L2 beams and their actual background time reverses with exactly that common extinction.
- Physical absorption difference approaches the parabola and the free-extinction relative supremum is one.

Exact interfaces: `GeneralizedResearch.PhysicalBeamCorollary.corollary65`, `GeneralizedResearch.PhysicalBeamCorollary.realizes`, `GeneralizedResearch.PhysicalBeamCorollary.actual_reference`, `GeneralizedResearch.PhysicalBeamCorollary.true_time_reverse`, `GeneralizedResearch.PhysicalBeamCorollary.radiation`, `GeneralizedResearch.PhysicalBeamCorollary.material_caps`, `GeneralizedResearch.PhysicalBeamUpper.corollary65_sSup`, `GeneralizedResearch.PhysicalBeamUpper.relative_one`.

The explicit normalized uniform disk aperture is sufficient for this existential corollary. The proof includes unitary Fourier normalization, regional Maxwell equations, all interfaces, actual incoming/outgoing expansions, material caps and physical net Poynting flux. It does not certify every arbitrary L2 aperture or a separate global distributional gluing theorem.

### generalized-research — Theorem 7.1

Status: `complete-source-and-final-replay-correspondence`.

- For every 0<rho<1 and X in [0,4], the full arbitrary-dimensional reciprocal passive channel maximum is the literal three-branch envelope.
- The middle c is the unique solution in (0,rho) to the printed rational equation, with the printed lambda.
- Two channels suffice in the first and middle branches; three suffice in the last branch.
- The formulas join continuously at both transitions.

Exact interfaces: `GeneralizedResearch.theorem71`, `GeneralizedResearch.theorem71_clm_reference`, `GeneralizedResearch.SmallAttainment.first`, `GeneralizedResearch.SmallAttainment.middle`, `GeneralizedResearch.SmallAttainment.third`, `GeneralizedResearch.SmallAttainment.At.neg`, `GeneralizedResearch.SmallAttainment.theorem71_dimension`, `GeneralizedResearch.OverlapParameters.middle_r`, `GeneralizedResearch.OverlapParameters.envelope_at_first_transition`, `GeneralizedResearch.OverlapParameters.envelope_at_second_transition`, `GeneralizedResearch.EnvelopeContinuity.envelope_continuous`.

The upper statement admits the literal reference condition S0-adjoint*S0=I: reciprocity derives the isometric reference surjectivity. Subsequent proof discussion of rho=0 or rho=1 and full equality classifications is outside the numbered theorem with 0<rho<1.

### quartic-maxwell — Theorem 1.1

Status: `complete-source-and-final-replay-correspondence`.

- Existence and AE uniqueness for every independently supplied locally finite-energy outgoing weak Maxwell state on every measurable admissible tensor support.
- Both exact bounds min(1, sharp volume expression) and min(1, enclosing-ball expression) at every k,R>0.
- Constants are uniform in arbitrary geometry, component count and material patterns that vary with R.

Exact interfaces: `QuarticMaxwell.PhysicalPowers.theorem11`, `QuarticMaxwell.PhysicalPowers.theorem11_ball`, `QuarticMaxwell.WeakMaterial.wellposed`, `QuarticMaxwell.WeakMaterial.state_representation`, `QuarticMaxwell.LocalTensorClass.zeroExtension_measurable`, `QuarticMaxwell.LocalTensorClass.matrixOperator_norm`, `QuarticMaxwell.LocalTensorClass.matrixOperator_reciprocal`.

### quartic-maxwell — Theorem 1.2

Status: `complete-source-and-final-replay-correspondence`.

- The literal same two finite spheres, centers minus/plus R*n/2, radii R/20 and R/10, susceptibilities i and 2i, satisfy m=1,M=2.
- Actual interacting continuum coefficient lies in [36/1299125,44/1295875].
- Exact remainder at most 21/2000*(kR)^6 through kR<=1/4 and lower bound 27/1299125*(kR)^4 through kR<=1/40.
- Every independently supplied physical outgoing weak state at fixed k uses the same spatial pattern for both illuminations.

Exact interfaces: `QuarticMaxwell.HeterogeneousCertificate.coefficient_interval`, `QuarticMaxwell.HeterogeneousAttainment.fixed_wavenumber_remainder`, `QuarticMaxwell.HeterogeneousAttainment.fixed_wavenumber_lower`, `QuarticMaxwell.PaperSignConvention.contrastPaper_eq`, `QuarticMaxwell.TwoSphereGeometry.medium_reciprocal`, `QuarticMaxwell.PhysicalDilation.state`.

### quartic-maxwell — Theorem 1.3

Status: `complete-source-and-final-replay-correspondence`.

- For every 0<m<=M, positive constants c,C,t0 are chosen before all real transverse unit pairs, physical k>0 and R>0.
- The actual admissible-design supremum lies between c*(kR)^4 and C*(kR)^4 below t0.
- The fixed lower pattern has exactly homogeneous susceptibility i*m on two unequal disjoint finite spheres, including M=m; its relative radii are chosen before shrinking.
- Every fixed real transverse pair is covered.

Exact interfaces: `QuarticMaxwell.HomogeneousSharpness.theorem13`, `QuarticMaxwell.HomogeneousSharpness.sSup_sandwich`, `QuarticMaxwell.HomogeneousSharpness.pattern_homogeneous`, `QuarticMaxwell.HomogeneousSharpness.pattern_admissible`, `QuarticMaxwell.HomogeneousMoments.chosenRadius`, `QuarticMaxwell.HomogeneousMoments.chosenParameters`.

A coordinate-free direct construction uses centers +/-n/2 for each real unit n and e perpendicular to n. This proves the original coverage assertion without requiring a separate abstract Maxwell rotation-covariance theorem.

### quartic-maxwell — Lemma 3.1

Status: `complete-source-and-final-replay-correspondence`.

- The actual distributional-contact static operator has norm at most one on every measurable support.
- The actual outgoing-minus-static operator has norm at most (3/4)*k^2*av^2, with av the exact volume radius.

Exact interfaces: `QuarticMaxwell.maskedStaticOperator_norm_le`, `QuarticMaxwell.maskedOutgoingOperator_difference_norm_le_volume`, `QuarticMaxwell.supportCurrent_outgoing_distribution`, `QuarticMaxwell.domainStaticOperator_norm_le`, `QuarticMaxwell.domainOutgoingOperator_difference_norm_le`.

### quartic-maxwell — Lemma 3.2

Status: `complete-source-and-final-replay-correspondence`.

- The complete sphere radiation transform is the actual transverse Fourier current integral.
- Exact imaginary-Green quadratic identity with coefficient k^3/(16*pi^2), nonnegativity and sharp radiation norm squared at most 8*pi*V/3.
- The actual incident-work, material-loss and complete outgoing-scattering cross sections have the stated constants and satisfy X=A+S.

Exact interfaces: `QuarticMaxwell.domainRadiationMap_norm_sq_le`, `QuarticMaxwell.maskedOutgoingOperator_imaginary_radiation`, `QuarticMaxwell.PhysicalPowers.state_power_balance`, `QuarticMaxwell.PhysicalPowers.scattering_physical_flux`, `QuarticMaxwell.compactCurrentFarField_eq_radiationField`, `QuarticMaxwell.compactCurrentFarField_power_eq`, `QuarticMaxwell.PhysicalPowers.absorption_eq_volume`, `QuarticMaxwell.PhysicalPowers.scattering_eq_volume`.

### quartic-maxwell — Lemma 3.3

Status: `complete-source-and-final-replay-correspondence`.

- The actual inverse susceptibility loss is at least m/M^2 times the identity.
- The actual common volume inverse has norm at most rho=M^2/m and the volume operator has the printed Lk norm bound.
- The volume solution is equivalent to every outgoing locally finite-energy weak Maxwell solution and is unique.

Exact interfaces: `QuarticMaxwell.VolumeInverse.negative_coercive`, `QuarticMaxwell.VolumeInverse.inverse_norm_le`, `QuarticMaxwell.VolumeInverse.operator_norm_le`, `QuarticMaxwell.WeakMaterial.wellposed`, `QuarticMaxwell.TensorMultiplier.inverse_loss_bound`, `QuarticMaxwell.TensorMultiplier.inverse_norm_le`.

### quartic-maxwell — Lemma 3.4

Status: `complete-source-and-final-replay-correspondence`.

- Actual opposite real plane waves have exactly equal extinction, and this common extinction is strictly positive for positive-volume supports.

Exact interfaces: `QuarticMaxwell.VolumeInverse.operator_reciprocity`, `QuarticMaxwell.PhysicalPowers.state_extinction_reciprocal`, `QuarticMaxwell.PhysicalPowers.theorem11`.

### quartic-maxwell — Theorem 4.1

Status: `complete-source-and-final-replay-correspondence`.

- Actual static uniform and affine responses and actual integral moments give a strictly positive D0.
- The coefficient is exactly 2*abs(Im(inner(p0,p1)))/(3*pi*D0).
- For every fixed material pattern, fixed physical k and every actual weak state on the dilated body, the error from C*(kR)^4 is at most a finite derived constant times (kR)^6 on a positive derived interval.
- If the moment numerator vanishes, the same estimate gives contrast O((kR)^6).

Exact interfaces: `QuarticMaxwell.FixedPatternContrast.fixed_pattern_quartic`, `QuarticMaxwell.FixedPatternContrast.coefficient_moment`, `QuarticMaxwell.FixedPatternDilation.fixed_wavenumber_quartic`, `QuarticMaxwell.FixedPatternDilation.interval_pos`, `QuarticMaxwell.PhysicalDilation.state`, `QuarticMaxwell.PhysicalDilation.absorption_scale`, `QuarticMaxwell.PhysicalDilation.extinction_scale`, `QuarticMaxwell.FixedPatternDilation.contrast_scale`, `QuarticMaxwell.FixedPatternWork.D0_pos`.

The zero-numerator clause is a specialization of the proved universal estimate, not a missing positivity assumption. coefficient_moment identifies C as 2*abs(Im(inner(p0,p1)))/(3*pi*D0); if that numerator is zero, rewriting C=0 in fixed_wavenumber_quartic gives |contrast|<=remainderConstant*(kR)^6. interval_pos gives a positive interval. No separate named zero-coefficient corollary is required for this logical implication.

## Numbered-statement boundaries

- Generalized Proposition 2.1 Eq6 and the zero-product clause occur before Proof and must be included.
- Generalized Theorem 6.3 Eq52 all-equality classification occurs before Proof and must be included.
- The full scalar optimizer/singular-spectrum classification after Proposition 2.2 is separately unnumbered.
- Remark 4.6 strictness of the finite-cell floor is separate from Theorem 5.1 strict finite-stack D<D0.
- Theorem 7.1 explicitly assumes 0<rho<1. Subsequent rho=0/rho=1 discussion and all-optimizer classifications have separate statuses.
- Quartic unnumbered matrix optical identity, sharper auxiliary Gram constant, causal discussion and numerical checks must retain their separate ledger statuses; numbered theorem completeness is not a claim that every manuscript sentence is certified.

## Proposed manuscript helper (read only)

The helper was inspected without execution. Its weak-Maxwell, tensor-layer, disk-aperture and same-kernel limitations are appropriate. Replace the ambiguous phrase “strict finite-resource nonattainment remark” with “strictness of the finite-cell resource-floor inequalities (Remark 4.6)”. Add full golden equality-family scope only after the new classification passes.

## Source-location checks

Every listed source exists; every listed declaration spelling occurs in that file. This mechanical check is only an inventory check, not Lean elaboration.
