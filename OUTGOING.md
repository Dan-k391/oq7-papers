# Physical outgoing volume operator

`FarFieldWorkL2.lean` proves outgoing-volume work equals the full vector
radiation integral with the actual Haar surface measure, for every original
compact L² current. The proof derives the scaled Poynting-flux error, computes
the radial cutoff's unit mass, passes the error to zero, and extends through
fixed-support smooth density using proved continuity. It also proves the
physical energy balance with that radiation integral. The conversion from
Haar surface measure to the original theta/phi formula is still unproved;
the original `scattering` identity is not yet claimed. Evidence:
`verification/milestones/physical-haar-radiation-work/`.

`FarFieldCurrent.lean` identifies the actual electric Green-current field's
leading amplitude with the original full vector physical far-field expression.
`FarFieldKernel.lean` derives its uniform displaced-source kernel error,
including the phase, inverse-distance amplitude, transverse projection, and
lower-order dyadic terms. The integrated error is uniform over the entire
observation sphere for every original compact L² current. The far field is
continuous in direction and bounded uniformly. This does not yet prove the
full angular scattering/work identity. Evidence:
`verification/milestones/physical-full-far-field/`.

`PhysicalAbsorptionWork.lean` identifies the original local dielectric
absorption integral with total-field/current work and proves the exact
physical work balance: extinction equals absorption plus outgoing-volume
work. Proved outgoing positivity gives absorption at most extinction.
`RankOneAbsorption.lean` identifies the active-material work with the exact
local loss-weighted scalar-current integral and proves the original physical
absorption's sine-squared factorization. The full angular radiation identity
still must identify outgoing-volume work with the original scattering integral.
`PhysicalResponseStability.lean` supplies quantitative residual and angle
response estimates with the established aperture/rotation-independent inverse
bound. No localization estimate is assumed or asserted by these bounds.
Evidence: `verification/milestones/physical-rotation-absorption/`.

`RotationResponse.lean` and `RotationExtinction.lean` prove the physical
incident-drive and solved-current sine factorizations and the exact
`physicalExtinction_sine_squared_factorization` for the original extinction
integral. `normalizedActiveResponse` is defined at every real angle, including
zero, and its norm has the aperture/axis-independent inverse bound. This is
an exact identity for the reconstructed physical fields, not an assigned power
law. Reciprocity, the full angular radiation identity, scattering
factorization, and uniform aperture localization remain unproved. Evidence:
`verification/milestones/physical-rotation-extinction/`.

`RankOneScattering.lean` also supplies actual physical scattering states for
the manuscript's intermediate tensors `I + alpha u u^T` and `I + beta v v^T`,
with positive imaginary parts of the two scalar coefficients. The explicit
scalar-current embedding and projection are proved adjoints and are isometric
for unit material axes. The compressed operator's inverse norm is bounded by
`1 / min (alpha.im / normSq alpha) (beta.im / normSq beta)`, independently of
aperture and axes. The resulting current is proved to solve the original
physical material volume equation; all three Maxwell field components and
the full uniform radiation condition are retained. These intermediate tensors
have null loss directions and are not advertised as final admissible bodies.
The positive isotropic-loss restoration and exact target construction remain
unproved. Evidence: `verification/milestones/rank-one-physical-scattering/`.

`ScatteringExistence.lean` now proves `materialVolumeEquation_exists` and
`physicalScatteringState_exists` for every original admissible finite body,
positive frequency, and either incident direction. The closed Hilbert space
is supported on the actual body domain. Its outgoing operator is the
compression of the identified physical operator. Strict tensor loss and
proved outgoing dissipativity give `materialBodyEquiv`, a genuine inverse
of `T_k - chi^{-1}`. `materialBodyEquiv_inverse_norm_le` bounds its norm by
`1 / min a.loss b.loss`, where the two loss constants come solely from the
actual constitutive tensors. The solution is converted to the original
physical fields, both weak Maxwell curls, and full uniform Silver–Müller
condition. No Maxwell solvability or volume equation is assumed in these
existence declarations. Exact statements and axiom exports are under
`verification/milestones/physical-scattering-existence/`.

`MaterialVolumeUniqueness.lean` proves that every compact L² solution of the
actual physical material volume equation satisfies the same invertible
body-domain equation. `materialVolumeEquation_unique_current` therefore gives
equality almost everywhere of any two such currents. This does not assert a
converse volume representation for arbitrary weak outgoing Maxwell states.
That stronger representation and uniqueness statement remains unproved.

Theorem 1.1 remains unproved. This milestone closes the outgoing kernel and
compact-current operator identification following the verified static operator.

The actual outgoing Hessian is the full Newton contact Hessian plus the locally
integrable dynamic remainder. `outgoing_dyadic_contact_identity` retains the
principal value and the exact minus-one-third diagonal Dirac contribution.
`outgoingVolumeDistribution_eq_staticFourier_add_remainder` proves the matching
identity for every original compactly supported vector L² current. The current
is not assumed smooth and is not assumed to solve a material equation.

`outgoingVolumeDistribution_on_ball_bounded_L2_realization` constructs the
physical operator on a compact ball, with norm bound
`1 + compactRemainderConstant k R`. The radius dependence is explicit; this
does not assert an aperture-independent operator norm.

`outgoing_helmholtz_fundamental_distribution` proves
`(Δ + k²) g_k = -δ₀`, and `potentialComponent_helmholtz_L2_distribution`
proves the exact equation for the actual convolution with every original L²
current. Both use the original continuous test-function distributions.

`DyadicMaxwellSource.lean` then proves the actual second-order Maxwell source
equation `(curl curl - k²) G_k p = k² p` and both first-order curl equations
with magnetic distribution `-ik curl(g_k*p)`. The current is still any original
compact L² current. This identifies the correct source equations; it does not
yet supply the pointwise radiation condition.

`YoungConvolution.lean` supplies the missing L¹-kernel/L²-current bound, with
actual convolution existence almost everywhere. `PolePointIBP.lean` proves
the shrinking inverse-distance-pole error is O(ε). `GreenFirstDerivative.lean`
uses this to identify the actual first Green derivative without a contact
term. `GreenGradient.lean` and `GradientCurrentPairing.lean` prove the actual
gradient/current convolution is locally L² and equals the distributional
first derivative of the original scalar volume potential. No current
smoothness or electromagnetic identity is assumed.

The proof chain includes shrinking smooth cutoffs, removable-point integration
by parts, actual outgoing/current Fubini pairings, dynamic remainder pairings,
the previously verified Newton operator, and commutation of distributional
Cartesian derivatives. No radiation, optical theorem, physical coercivity,
Maxwell existence or localization assumption occurs in these declarations.

Evidence is in `verification/milestones/outgoing-dynamic-identity/`,
`outgoing-volume-identification/`, `compact-outgoing-operator/`,
`outgoing-fundamental/` and `volume-fundamental/`. Each contains the exact
principal types, transitive axiom export and build log. The complete library
census, including private constants, is in `verification/axioms.log`; the
clean project build is in `verification/clean-build.log`.

Reproduction: configure the exact pinned dependencies as in README, then run
`./verify.ps1 -Clean` and `./verify-milestones.ps1` with the pinned Lean binary.

Still required: exterior representatives
and pointwise outgoing representation; full-sphere radiation, passivity and
reciprocity; physical solution existence and uniqueness; uniform localization;
planar synthesis and both exact-extinction adjustments. None follows merely
from the scalar Helmholtz or bounded electric-operator identities.

PhysicalSourceFields.lean constructs actual locally L² electric and magnetic
source fields and proves both original scalar-distribution curl equations.
The electric representative uses the identified static L² operator plus the
actual remainder convolution. Radiation requires an exterior representative;
no pointwise claim is inferred from an almost-everywhere L² equality.

WeakCurlBridge.lean proves both physical source curl equations against every
smooth compact complex vector test, with all integrability justified. The test
regularity annotation in Maxwell.lean is strengthened to explicit ENat top;
untyped top in the pinned Mathlib meant analytic regularity. The exact earlier
source and the formal strengthening proof are saved and audited. This fixes
the physical weak equations without changing Theorem11Statement quantifiers.

RadiationKernel.lean proves the exact single-source Silver–Müller defect and
the uniform displaced-source bound for every source in a radius-R ball and
every observation direction, with explicit k/R dependence. The magnetic kernel
is identified with the actual outgoing gradient. These kernel estimates must
still be integrated and connected to the original L² field representatives.

ExteriorOutgoing.lean now integrates these bounds against every original
compact L² current. Both far-zone convolutions are proved integrable, and
exteriorCurrentFields_outgoing proves exactly the full-sphere uniform
Silver–Müller condition. Equality with the global L² weak-source fields,
especially the electric representative, is still required before assembling
a single global outgoing weak-Maxwell pair.

ExteriorKernelTests.lean identifies the full dyadic distribution on actual current correlations from exterior tests. Absolute integrability is proved and the contact term vanishes by the proved zero correlation at the pole. Connecting this test identity to the pointwise exterior electric convolution is the next obligation.

ExteriorCurrentIdentification.lean proves both Fubini steps, actual exterior electric test pairing, local integrability on the exterior open set, and electricExterior_eq_ae. The classical outgoing electric convolution is thereby identified with the global L2 source representative on that exterior domain.

OutgoingSourceFields.lean proves pointwise exterior magnetic identification, selects the actual exterior electric representative, and proves outgoingPhysicalSourceFields: both actual local L2 fields, both physical smooth-vector-test weak curls, and the full pointwise uniform Silver-Muller condition. Source solvability is complete for arbitrary compact L2 polarization; material scattering solvability and outgoing uniqueness are separate remaining obligations.

IncidentMaxwell.lean proves the exact incident plane-wave curl equations in both directions and all local L2 bounds. A reusable integration-by-parts bridge proves that any smooth classical curl gives the original physical weak curl, with compact-test integrability established.

PhysicalPolarization.lean proves the actual constitutive polarization of every locally L2 electric field on a finite TwoLayerBody is globally L2 and vanishes outside the proved support ball. physicalCompactPolarization packages this input without assuming a scattering state.

VolumeScatteringBridge.lean proves scatteringStateOfVolumeEquation from the explicit genuine current equation p = chi times (Einc plus T_k p). Maxwell equations, pointwise radiation, and compact-current L2 membership are established by the constructor. The hypothesis is not claimed solved: material-volume solvability, uniqueness, and optical identities remain open.

ComplexCoerciveInverse.lean proves complex Hilbert-space invertibility and inverse bounds from imaginary coercivity, by real Lax-Milgram and a rigorous complex rotation. TensorLossCoercivity.lean derives uniform quadratic coercivity on the actual vector space from the original strict tensor-loss condition and proves a bounded inverse of every admissible susceptibility T-I. This constitutive inverse does not establish material scattering solvability: positivity of the actual outgoing volume operator is still required. A fresh clean project build and transitive axiom audit passed; Theorem11Statement remains unproved.

CompactCurrentDensity.lean proves arbitrary L2 approximation by smooth currents inside a single fixed enlarged support ball. SmoothOutgoingFields.lean proves smoothness of the genuine scalar Green potential, identifies smooth electric and magnetic representatives with the physical source fields almost everywhere, and derives both pointwise Maxwell source equations from the already proved distribution identities. This prepares the cutoff energy argument; outgoing operator dissipativity and material scattering solvability remain unproved. The project build and transitive axiom audit passed for this milestone.

PoyntingCutoff.lean derives the exact compact-cutoff energy identity for the actual smooth-current Maxwell source fields. Conjugation, the curl product rule, source work signs, and integrability of both weak-curl pairings and the weighted work are proved. The identity is not an assumed optical theorem. The vanishing radial error and the subsequent L2 dissipativity extension remain required. Full project compilation and transitive axiom auditing passed.

RadialEnergyCutoff.lean and RadiationEnergyBounds.lean prove the actual radial energy identity, magnetic 1/r decay and full-direction flux lower bounds. SmoothOutgoingDissipativity.lean bounds the integrated error by C/r using the genuine three-dimensional ball measure and passes to infinity. OutgoingDissipativity.lean extends the result through fixed-support smooth approximation and the bounded physically identified operator: physicalOutgoingVolume_work_nonneg and compactOutgoingOperator_im_nonneg hold for every original compact L2 current at k>0. No physical dissipativity assumption is used. A fresh clean build (3373 jobs) and transitive axiom audit passed. Material equation solvability, outgoing uniqueness, the full optical theorem, uniform aperture localization and the prescribed-extinction construction remain open.

SphericalCoordinates through SphericalAngular prove the actual three-dimensional spherical change of variables: derivative, Jacobian r² sin(theta), injectivity, coverage outside a null plane, product-volume transport, radial unit mass, and azimuth periodicity. PhysicalOpticalBalance identifies the exact original theta/phi scattering expression with the actual Haar radiation integral and proves physicalVolume_energy_balance (original extinction = absorption + scattering) for every actual material-volume solution. No optical identity or surface-measure conversion is assumed. The final Theorem11Statement remains unproved; reciprocity, uniform aperture localization, and the prescribed-extinction construction remain required.

LorentzCutoff and LorentzIdentity derive the complex, unconjugated compact-cutoff Lorentz identity from the actual Maxwell source curls. LorentzBounds proves cancellation of the leading radial terms and a genuine O(r^-3) mixed outgoing flux estimate, with a weighted O(r^-4) bound. SmoothReciprocity integrates the actual three-dimensional shell, proves the boundary error vanishes as C/r, and derives smooth-current Maxwell reciprocity. ReciprocityL2 extends this exact physical identity to arbitrary compact L2 currents through a joint continuous operator pairing and fixed-support smooth approximation. The physical outgoing operator's reciprocity is proved at every positive frequency; equality of opposite-direction material extinction is the next obligation.
