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

Still required: actual locally square-integrable magnetic fields; weak Maxwell
and pointwise outgoing representation; full-sphere radiation, passivity and
reciprocity; physical solution existence and uniqueness; uniform localization;
planar synthesis and both exact-extinction adjustments. None follows merely
from the scalar Helmholtz or bounded electric-operator identities.
