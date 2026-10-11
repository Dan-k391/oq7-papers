# Physical outgoing volume operator

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

Still required: weak Maxwell
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
