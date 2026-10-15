# Quartic formalization changes — 2026-10-14–2026-10-15

All entries below are new files under `papers/quartic-maxwell/formalization/`. The historical original paper, original arithmetic audit and prescribed-extinction proof sources are preserved. Later publication revisions and their source/PDF hashes are recorded separately after proof verification.

| File | Change |
| --- | --- |
| `lakefile.toml`, `lean-toolchain` | Separate Lean package, with the unchanged Lean/Mathlib pins inherited through the prescribed-extinction dependency. |
| `QuarticMaxwell/Certificates.lean` | Includes the preserved scalar arithmetic certificate with its existing, limited scope. |
| `QuarticMaxwell/Operator.lean` | Common-inverse current estimates, radiation quadratic difference, conditional exact quartic operator bound and absorption bound. |
| `QuarticMaxwell/Asymptotics.lean` | Explicit sixth-order quotient error, positive-coefficient lower bound and translation-invariant moment coefficient. |
| `QuarticMaxwell/GreenEigenvalues.lean` | Exact complex-exponential cancellation and sharp scalar dynamic Green eigenvalue bounds. |
| `QuarticMaxwell/ProjectionGeometry.lean` | Orthogonal radial/tangential vector norm estimate. |
| `QuarticMaxwell/ProjectionKernel.lean` | Exact actual dyadic Green projection decomposition and sharp `3k²/(8πr)` kernel norm. |
| `QuarticMaxwell/MaterialInverse.lean` | Complex Hilbert-space coercive inverse, `1/m` norm and `m/M²` inverse-loss estimate. |
| `QuarticMaxwell/Rearrangement.lean` | Equal-volume measurable-set threshold rearrangement. |
| `QuarticMaxwell/SharpVolume.lean` | Actual three-dimensional ball volumes and Newton integrals, with sharp uniform bounds for arbitrary bounded measurable supports. |
| `QuarticMaxwell/Schur.lean` | Vector L² Schur integral-operator estimate with integrability proved from the kernel majorants. |
| `QuarticMaxwell/MaskedRemainder.lean` | Actual support-masked outgoing/static operators, physical outgoing-distribution correspondence and manuscript Lemma 3.1 norm estimates. |
| `QuarticMaxwell/RadiationMoment.lean` | Exact complex-vector transverse-projection moment on the actual sphere area measure. |
| `QuarticMaxwell/SquareIntegral.lean` | Finite-measure vector integral Cauchy–Schwarz estimate. |
| `QuarticMaxwell/RadiationOperator.lean` | Actual complete vector radiation map, derived joint integrability and sharp squared norm `8πV/3`. |
| `QuarticMaxwell/RadiationPhysical.lean` | Exact identification of that map with the genuine compact-current electric far field and its complete angular power normalization. |
| `QuarticMaxwell/IncidentSources.lean` | Actual opposite plane waves, exact source L² norm and source-difference estimate. |
| `QuarticMaxwell/RadiationIdentity.lean` | Exact imaginary outgoing-Green work identity, using the actual complete far field. |
| `QuarticMaxwell/Reciprocity.lean` | Genuine Green bilinear reciprocity, actual vector conjugation and incident-wave conjugation. |
| `QuarticMaxwell/SupportedOperators.lean` | Closed supported L² space, actual restricted static/outgoing/radiation operators, actual current association and supported reciprocity. |
| `QuarticMaxwell/TensorMultiplier.lean` | Actual measurable tensor field multiplier and inverse, exact constitutive relation, norm and loss resource bounds. |
| `QuarticMaxwell/VolumeInverse.lean` | Actual single Maxwell volume inverse with resource constants, tensor reciprocity and actual constitutive solution. |
| `QuarticMaxwell/UniformBound.lean` | Exact material-class uniform quartic contrast and `min 1` bound from derived analytic and material premises. |
| `QuarticMaxwell/BallBound.lean` | Actual containing-ball volume comparison and exact `8/9` bound. |
| `QuarticMaxwell/PlaneWaves.lean` | Actual transverse incident electric/magnetic plane waves satisfy the distributional Maxwell curl equations. |
| `QuarticMaxwell/WeakMaterial.lean` | Actual arbitrary-tensor outgoing weak Maxwell existence, converse volume representation and uniqueness for every independently supplied state. |
| `QuarticMaxwell/PhysicalPowers.lean` | Literal absorption/extinction integrals, complete far-field and Poynting power, energy balance, reciprocity, positivity and both original Theorem 1.1 inequalities for every weak state. |
| `QuarticMaxwell/StaticInverse.lean` | Actual static material inverse, positive static forward work and exact dynamic/static resolvent error. |
| `QuarticMaxwell/SourceTaylor.lean` | Actual bounded-support constant, cosine, sine and affine sources; derived pointwise/L² Taylor remainders and real-source conjugation. |
| `QuarticMaxwell/RadiationGram.lean` | Actual complete-angle adjoint Gram operator, exact antipodal evenness, zero-frequency integral moment identity and source/moment pairing. |
| `QuarticMaxwell/RadiationTaylor.lean` | Derived actual radiation-field differences and even remainders from the phase Taylor estimates and exact sphere moments. |
| `QuarticMaxwell/GramEstimates.lean` | Actual Gram norm and second-order difference bounds; the displayed sharper diameter constant remains a separate unproved auxiliary claim. |
| `QuarticMaxwell/StaticReciprocity.lean` | Actual static Green and static material-inverse bilinear reciprocity, derived from dynamic reciprocity and norm convergence. |
| `QuarticMaxwell/FixedPatternWork.lean` | Actual even/odd volume-response errors, positive static denominator and quantitative common forward-work expansion. |
| `QuarticMaxwell/FixedPatternScattering.lean` | Actual full-angle signed scattering difference, exact static moment coefficient and explicit cubic numerator error. |
| `QuarticMaxwell/FixedPatternContrast.lean` | Physical absorption contrast equals the derived quotient for every weak state; explicit positive small-frequency interval and sixth-order remainder, including a zero coefficient. |
| `QuarticMaxwell/LocalTensorClass.lean` | Actual local-measurability zero extension and literal matrix/complex-linear-operator norm and transpose bridges. |
| `QuarticMaxwell/StaticHessian.lean` | Actual classical Newton-Hessian entries, measurability, sharp `1/(2πr³)` operator norm and separated-point `6/(πd⁴)` Lipschitz estimate. This does not assume static cross-block identification. |
| `QuarticMaxwell/PhysicalDilation.lean` | Actual three-dimensional Jacobian, local L², weak curl, outgoing-state and material scaling, with literal absorption/extinction area factors. |
| `QuarticMaxwell/FixedPatternDilation.lean` | Original fixed physical wavenumber and shrinking-body quartic coefficient/remainder for every independently supplied weak Maxwell state, using genuine dilation and uniqueness. |
| `QuarticMaxwell/CrossBlockOperator.lean` | Actual rectangular Newton-Hessian integral operator, almost-everywhere kernel representation and sharp sqrt(V1*V2)/(2πd³) norm. |
| `QuarticMaxwell/BlockResolvent.lean` | Exact generic block-resolvent algebra, small-coupling inverse comparison and unconditional second-order reflection remainder. |
| `QuarticMaxwell/SphereNewton.lean` | Actual three-dimensional solid-ball Newton potential, including interior/exterior formulas derived from spherical integration. |
| `QuarticMaxwell/SphereStatic.lean` | Distributional identification of the actual static Fourier operator on a constant ball current, yielding the exact -1/3 eigenresponse. |
| `QuarticMaxwell/SphereResponse.lean` | Actual scalar-material ball inverse, beta=3χ/(3+χ), and exact arbitrary-input integrated response. |
| `QuarticMaxwell/StaticOffSupport.lean` | Separated-support Newton integration by parts and almost-everywhere Fourier-static Hessian kernel representation. |
| `QuarticMaxwell/StaticCrossIdentification.lean` | Exact equality of the physical static cross block and the constructed Hessian integral operator; sharp cross-block norm. |
| `QuarticMaxwell/SupportBlocks.lean` | Actual supported-L² union decomposition, orthogonal inclusions/projections, diagonal and off-diagonal operator identities and sharp block norms. |
| `QuarticMaxwell/TwoSupportStatic.lean` | Actual piecewise scalar susceptibility and exact single static inverse/block interaction identity. |
| `QuarticMaxwell/TwoSupportBounds.lean` | Derived actual interaction bounds, static inverse comparison and second-order all-reflection remainder. |
| `QuarticMaxwell/TwoSphereGeometry.lean` | Actual unequal-ball geometry for arbitrary incident direction, exact volumes/separation, admissible medium and delta<1/600. |
| `QuarticMaxwell/SphereExterior.lean` | Actual exterior constant-ball Newton/Green field and exact Hessian field identification. |
| `QuarticMaxwell/SphereHessianMean.lean` | Actual exterior single-ball Hessian harmonic mean identity. |
| `QuarticMaxwell/SphereDoubleMean.lean` | Actual double-ball Hessian mean identity for separated finite spheres. |
| `QuarticMaxwell/BallAffineMoments.lean` | Actual ball linear/quadratic moments, centered odd affine source, exact L² norm and weighted-current bounds. |
| `QuarticMaxwell/MomentOperator.lean` | Actual supported-current integral as a continuous linear map, with sqrt(V) norm and derived response-difference estimate. |
| `QuarticMaxwell/BlockSourceMoments.lean` | Actual constant/affine restrictions, inclusion moment identities and exact arbitrary-input isolated-block moment formulas. |
| `QuarticMaxwell/QuantitativeQuotient.lean` | Sixth-order quotient remainder using independently proved common lower bounds on both actual denominators. |
| `QuarticMaxwell/HeterogeneousCertificate.lean` | Actual interacting continuum moments, exact isolated scalar values, derived perturbation enclosures and the original rational coefficient interval. |
| `QuarticMaxwell/HeterogeneousRemainder.lean` | Derived actual finite-family response/Gram bounds and exact scattering/forward-work error constants. |
| `QuarticMaxwell/HeterogeneousAttainment.lean` | Full original Theorem 1.2: exact coefficient interval, quantitative remainder/lower bound and physical fixed-k versions for every weak state. |
| `QuarticMaxwell/SphereCrossMoment.lean` | Actual finite-sphere cross moments and zero-mean kernel cancellation bounds. |
| `QuarticMaxwell/BlockInteractionMoments.lean` | Exact actual first constant/affine interaction moments and centered-odd response estimates. |
| `QuarticMaxwell/HomogeneousScalars.lean` | Exact homogeneous beta formulas, bounds, positive imaginary part and positive leading coefficient arithmetic. |
| `QuarticMaxwell/MomentPerturbation.lean` | Generic complex inner-product perturbation, positive-small-radius existence and higher-power error collapse; actual sphere estimates are proved separately before instantiation. |
| `QuarticMaxwell/StaticHessianExact.lean` | Actual unit radial eigenvector attains the sharp Newton-Hessian operator norm, proving equality. |
| `QuarticMaxwell/HeterogeneousAuxiliary.lean` | Actual delta-dependent moment errors, strict relative error below one tenth and certified outward-rounded decimal coefficient endpoints. |
| `QuarticMaxwell/PaperSignConvention.lean` | Exact exp(+ikn.x) physical incident labels, original signed leading coefficient, actual scattering-sign correspondence and equality of the paper/library absorption contrasts. |
| `QuarticMaxwell/LorentzMaterial.lean` | Literal Lorentz denominator zeros strictly below the real axis, positive real-frequency loss and exact operating value ij; no separate time-domain causality theorem is asserted. |
| `QuarticMaxwell/SharpnessClass.lean` | Actual admissible physical design class and supremum, uniform fixed-resource upper bound, genuine scaled lower families and supremum comparison. |
| `QuarticMaxwell/HomogeneousMoments.lean` | Actual homogeneous unequal-sphere continuum moments, constant/affine isolated responses, exact first interaction and original positive ninth-order leading term. |
| `QuarticMaxwell/HomogeneousErrors.lean` | Derived actual affine and all-reflection moment errors, including every static multipole. |
| `QuarticMaxwell/HomogeneousCoefficient.lean` | Actual positive continuum coefficient with one relative radius depending only on material resources, uniformly over real transverse unit illumination pairs. |
| `QuarticMaxwell/HomogeneousUniform.lean` | Actual homogeneous D0 lower bound and material constants, with a rigorously positive mu=1,a=1/100 example. |
| `QuarticMaxwell/HomogeneousBounds.lean` | Derived resource/radius-only numerator and denominator errors, coefficient floors, uniform cutoff and physical lower bounds for all independently supplied weak states. |
| `QuarticMaxwell/HomogeneousSharpness.lean` | Full original Theorem 1.3: actual physical admissible-class supremum has resource-only two-sided quartic bounds, with constants preceding every real transverse unit pair and all k,R. |
| `QuarticMaxwell/HomogeneousQuantitative.lean` | Original exact relative-error certificate, explicit 5277/175000 example, existence of a fixed quantitative radius and literal two-sided homogeneous coefficient interval. |
| `QuarticMaxwell.lean`, `Audit.lean` | Aggregate imports and human-readable selected proof inspection commands. The generated inventory below is exhaustive. |
| `verify.py` | Pinned compilation, global proof-escape rejection, exhaustive declaration types/axioms including inline attributes, missed-declaration and module-census rejection, required-public-root and exact physical core theorem type guards, coverage/manifest mutation rejection, source hashes and optional fresh replay through Lean's own kernel checker. |
| `verification/` | Generated checked-source report, exact all-declaration inventory and compiler/kernel logs. |
| `verification/dependency-source-binding.json` | Exact 376-source preserved dependency snapshot, unchanged-through-run check, dependency configuration/aggregate hashes, clean pinned Mathlib and exact Lean/checker binary hashes, bound to the final proof report. |
| `verification/coverage.json`, `verification/public-roots.json`, `verification/core-theorem-types.json` | Exact dated-PDF and reading-revision hashes, 92-entry claim/equation ledger, 128 required public exports and full-type SHA/string guards for 20 physical roots covering all eight numbered claims; restricted auxiliary claims remain explicit. |
| `verification/checkpoints/upper-fixed-pattern-2026-10-14/` | Separate successful fixed-pattern record: all 39 ingredient modules, aggregate, all 487 exact public types/axioms, fresh-kernel replay and copies of the checked proof sources. |
| `verification/staging/StagedSphereAudit.*` | Separate exhaustive sphere-stage exact type/standard-axiom inventory, with exact source hashes. |
| `verification/checkpoints/upper-2026-10-14/` | Separate successful upper-bound record: all 26 ingredient modules, aggregate, 300 exact public types/axioms and fresh-kernel replay, with source hashes and verifier snapshot. |
| `verify_type_controls.py`, `verification/negative-controls/type-guards-report.json` | Seven isolated expected rejections for changed physical constants, weakened sharpness, missing core claims/roots/types, corrupted type hashes and duplicate type inventories; 20 baseline exact types pass. |
| `verification/checkpoints/all-numbered-theorems-2026-10-15/` | Final successful 76-ingredient-module checkpoint, 1,048 exact public types/axioms, 20 physical root type guards, 128 required roots, fresh replay and complete checked-source copies. |
| `verify_negative_controls.py`, `verification/negative-controls/` | Portable `--lean-bin` selection (also passed to the census test) and five isolated rejection controls: prohibited proof placeholder, local axiom, deliberately false equality proof, accepted-but-untrusted axiom and missing module census. Control sources stay in ignored scratch. All controls passed. |
| `README.md`, `CLAIM_STATUS.md` | Exact theorem correspondence and remaining physical obligations, with all numbered theorem cores verified and the separate whole-paper completion flag explicitly false. |

All original numbered theorem and lemma cores are fully verified in the final 76-module, 1,048-export checkpoint, with exact physical type guards, standard-axiom inventories and successful fresh kernel replay. This includes the actual weak-Maxwell arbitrary-tensor uniform bound, fixed-k shrinking-body coefficient theorem, heterogeneous quantitative finite-sphere attainment and homogeneous every-resource sharpness with resource-only constants uniform over every real transverse unit incident pair. Original homogeneous quantitative relative-error and coefficient constants are also derived. Twelve isolated rejection controls passed; previous control records and checkpoints remain preserved byte-for-byte. Restricted auxiliary displays and empirical/bibliographic/human-review claims retain their separate ledger status, so no whole-paper verification claim is made. The preserved manuscripts, historical arithmetic audit and original prescribed-extinction project remain unchanged.
