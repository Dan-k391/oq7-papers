# Independent Audit B: counterexamples and edge cases

Date: 10 October 2026. This audit was written before reconciliation with the analytical and model-fidelity audits. Both manuscripts, including all appendices and references, were read in full. The reasoning and numerical implementation here are independent of the manuscripts' claimed outcomes and supplied numerical programs. This is an AI-agent mathematical review, not independent human peer review or a Lean certificate.

## Verdict

No fatal counterexample or genuine proof error was found in Paper B Theorem 3.1 or Proposition 3.8 under their exact fixed-stack, strictly absorbing hypotheses. The grazing singularity is real and rules out two tempting stronger operator statements, but the manuscript explicitly avoids those statements. The local mixed-norm commutator estimate survives those tests. The compact supremum implication survives this audit once that ordinary analytical proof is accepted. This verdict does not certify formal verification or novelty.

Paper A Theorem 7.1 also survived: its complete generalized middle-branch certificate and exact rational example pass independent exact symbolic checks; all three equality constructions and transitions pass direct algebraic review. Its theorem concerns abstract reciprocal contractions, and no local Maxwell realization follows from this audit. Paper A Theorem 5.1 survived an independent review of its hypotheses and full proof, plus an 80-digit exact-layer benchmark, but the numerical root solve is not an implicit-function proof or a formal proof of the supremum law.

## Paper B: analytical falsification attempts

### A genuine grazing obstruction, correctly avoided

At transverse frequency `kappa=(rho,0)`, choose the TE profile `q(z)=e_y` on `(0,L)`. By the Weyl fiber, the leading term as `beta=sqrt(k^2-rho^2)` tends to zero is

`T_kappa q(z) = i k^2 L e_y/(2 beta) + O(1)` in `L2(0,L)`.

Indeed, `integral_0^L exp(i beta |z-z'|) dz' = L + O(beta)` uniformly in `z`. Let `g` be a nonnegative, nonzero, smooth compactly supported transverse function with support in a disk of radius less than `pi/(2k)`. Its Fourier transform is positive at `kappa=(k,0)` because the cosine is positive throughout the support; it stays nonzero on a neighborhood. TE projection of `e_y` also stays nonzero there. Subtracting the bounded `T_0 q` term does not cancel the singular term. Consequently

`integral |g_hat(kappa)|^2 ||(T_kappa-T_0)q||_H^2 d kappa = infinity`,

since the squared singularity contains `integral_0^epsilon ds/s`. Thus a full transverse `L2(R2;H)` bound on this commutator would be false for suitable compact smooth sources. This is an analytical counterexample to a *stronger statement absent from the paper*, not to Lemma 3.6. Paper B p.9 explicitly notes nonintegrability of the square; p.10–11, equations (44)–(48), uses Plancherel only below `k/2`, and uses the locally integrable unsquared fiber norm in the high-frequency `L1 -> L-infinity` estimate. Restriction to the finite aperture then supplies the factor `R`. Those are the correct domains.

The separate high-precision numerical experiment excises progressively smaller neighborhoods of the grazing circle in a Gaussian-weighted leading TE model. The `L1` integral stays bounded, while the squared integral grows logarithmically. Its observed slope `0.57786367489546085895536...` agrees with the exact asymptotic `pi/(2e)`. The Gaussian test is a truncated numerical model; the compact-source divergence above is the actual analytical counterexample.

### Green norms are not aperture-uniform, while the inverse bound is

One can show analytically that `||T_R||` need not stay bounded. Set `k=L=1` and take `P_R=e_y exp(ix)` on a side-`R` square prism. In the radiation identity, consider the positive-direction patch

`|n_y| <= a/R`, `|n_z| <= a/sqrt(R)`, `n_x=sqrt(1-n_y^2-n_z^2)`,

with a sufficiently small fixed `a>0`. The source Fourier integral has magnitude at least a fixed positive multiple of `R^2` throughout this patch: its three exact sinc arguments remain in intervals where sinc is bounded below. The transverse projector retains a fixed fraction of `e_y`. The patch solid angle is at least a fixed multiple of `R^(-3/2)`. Equation (20) therefore gives

`Im <P_R,T_R P_R> >= C R^(5/2)`, whereas `||P_R||^2=R^2`.

Hence `||T_R|| >= C sqrt(R)`. The numerical positive-patch calculation records the same scaling. This is again a counterexample to an unclaimed stronger uniform-Green estimate: Lemma 3.2 p.7 says its constant need not be uniform. Proposition 3.3 pp.7–8 obtains `||L_R^-1|| <= K^2/delta` from `-Im <P,L_R P> >= (delta/K^2)||P||^2`, which does not require a uniform bound on `||T_R||`. The coercivity sign, inverse-susceptibility factorization, and dependence on the fixed parameters check out.

The dependence on the loss floor cannot in general be removed. For the permitted planar susceptibility `chi=(-1+i delta) I`, the longitudinal fiber is `T_0=-I`; on longitudinal profiles the inverse of `chi^-1-T_0` is multiplication by `chi/(1+chi)`, whose magnitude is `sqrt(1+delta^2)/delta`. Thus uniformity as `delta -> 0` fails even for this fixed planar geometry. Theorem 3.1 and Proposition 3.8 expressly exclude that uniformity.

### Sharp aperture, rate, and order of limits

Lemma 3.6 estimates a smooth trial current and does not smooth the actual material boundary. The residual identity (49) and aperture-independent inverse bound allow the trial-window boundary discrepancy to be controlled in `L2`. For fixed `g`, low frequencies give `O(1)` and high frequencies give `O(R^(3-N))`; taking `R -> infinity` before approximating one in `L2(Omega)` therefore proves (52). Density uses no uniform derivative bounds for sharpening windows.

For the square cutoff, five pure derivatives have `L1` bound `C R w^-4`. A mixed derivative of total order five is `O(w^-3) <= C R w^-4` when `w<=R/8`. These give the three residual terms `(Rw)^(1/2)`, `(R/w)^(1/2)`, and `R^2 w^-4` in (61). At `w=k^-1(kR)^(1/3)`, their fixed-`k` orders are `(kR)^(2/3)`, `(kR)^(1/3)`, and `(kR)^(2/3)`. The rate (57)–(58) is dimensionally consistent because its constants retain the necessary fixed units and dependence on `k,L,K,delta`. It is an upper estimate, not an optimal rate or a uniform diagonal-sequence resource law.

The limit from currents to extinction is a bounded linear-form estimate, and the absorption limit is a bounded quadratic-form estimate using fixed `W`. Total scattering is recovered by subtracting the complete finite and planar optical identities, so the proof does not discard edge diffraction, a narrowing forward peak, grazing radiation, or a polarization channel. No invalid pointwise far-field convergence assumption was found.

The two-layer construction (pp.13–16) retains all four planar channels and the vacuum-reference transmission phase. Positive loss is fixed before enlarging the aperture. Its extinction density is positive for each fixed regularized stack, making the quotient limit valid; no uniform lower extinction bound is asserted. The loss caps can be respected for every fixed `P>1,Q>0` by first selecting a finite slab and then selecting a sufficiently small positive regularization. The point `P=1` and a common positive lower loss bound are different hypotheses and are not covered by the theorem.

## Paper A edge checks

The scalar modulus comparison does not need a lower bound on real permittivity for its stated use in Theorem 4.5; its upper bound `p<=P` is what fixes the comparison frequency. The capped moment bound includes zero mass and a full-period saturated density. The global-tangent argument correctly avoids Jensen on the nonconvex part of `[0,pi]`. The physical matching construction uses finite positive quarter-wave thicknesses; the negative exponentials in the stripped core are algebraic factors. The strict active-branch assumptions of Theorem 5.1 exclude `T=0`, `a=0`, the branch transition, and `P=1`, where its matching argument can degenerate. No extension to those endpoints was inferred.

For Theorem 7.1, independent symbolic algebra verifies the generalized Sylvester identity, determinant of `Z`, support identity, lambda identity, and derivative of the middle parameter map. At `rho=4/5`, `r=59/95`, `c=2/5`, and `lambda=2/19`, every displayed rational certificate identity vanishes exactly. The contrast is exactly `1071 sqrt(21)/9025 = 0.543815907955424...`, below `3/5`. The first-branch plateau is attained by a phase times a rank-one projection. The third-branch real symmetric three-channel construction directly maps the designated reversed input to `r` times the other and saturates the latter's output norm. The branches meet at `r=rho/2` and `r=rho`; `rho=0,1` are correctly treated separately. These are abstract matrix conclusions.

## Reproducible independent experiments

Sources: `numerics/audit_b_checks.py`. Complete observed values and versions: `numerics/audit_b_results.json`. The script imports no manuscript program and uses a fixed seed. It was run with Python 3.12.15, NumPy 2.5.3, SciPy 1.18.1, SymPy 1.14.0, and mpmath 1.3.0. Reproduction command from the research root:

```powershell
& 'C:\Users\Daniel\Documents\Codex\2026-10-09\set-up-a-local-ai-mathematical\outputs\math-research-lab\.venv\Scripts\python.exe' 'outputs\oq7-mission\numerics\audit_b_checks.py'
```

The old mathematical environment is used read-only. No prior proof source was modified. A separate environment with the listed dependencies can run the same script.

| Experiment | Observed result | Evidentiary scope |
|---|---|---|
| General and rational Theorem 7.1 identities | All exact symbolic remainders zero | Exact finite algebra, not the channel compression theorem |
| Random complex symmetric contractions, singular and unitary cases, overlaps from `10^-6` to `0.999999` | 12,000 samples; no violation | Floating-point falsification search, not proof |
| Planar set A, stable cascade and independent 4x4 exponential boundary solve | Gamma `0.7821175026664408`; maximum power discrepancy `1.89e-15` | Exact planar models evaluated numerically |
| Planar set B, same independent methods | Gamma `0.9180596086651859`; maximum power discrepancy `3.33e-15` | Exact planar models evaluated numerically |
| Regularized planar sequence, `m=100`, `P=4` | Gamma `0.9949932788539454` | Infinite planar sample, not a compact body |
| Same sample, `P=1.01`, `j=101` | Gamma `0.9949932472832498` | Tests the small real-cap construction |
| Paper A rational thickness family, 80 digits, `m=128` | `m^2 deficit=0.05000020535299`; `m^2 c=0.08333269048662` | Exact-layer numerical matching approaching `1/20` and `1/12`; no supremum proof |
| Full-sphere electric–magnetic dipole quadrature | Agreement with complete quadratic radiation; radiation dressing checked | Actual six-coordinate dipole model, not a local dielectric completion |
| Dense nonperiodic DDA, seven small geometries | Optical balance error at most `2.98e-14`; independent sphere radiation error at most `1.49e-14` | Solved finite dipole systems, not continuum-converged bodies |

The independent DDA shows why a small solver residual is insufficient for continuum certification. At side `R=lambda`, Gamma changes from `0.265441190566` at four cells per wavelength, to `0.456967278753` at six, to `0.514740475364` at eight. At a fixed coarse mesh of four cells per wavelength, increasing side from one to 1.5 wavelengths actually decreases the sampled ratio (`0.26544` to `0.24158`). This is no analytical counterexample: a fixed coarse point-dipole model is a different object from the continuum slab, and the theorem asserts convergence, not monotonicity. At six cells per wavelength the sampled ratio increases (`0.45697` to `0.49558`). No mesh error bars, convergence order, or continuum certification are claimed.

The manuscript's large FFT/GMRES tables and failed iterative runs were not reproduced by this small dense solver. Without the corresponding actual source and saved histories, their exact provenance remains unverified by Audit B; their printed diagnostics are not proof obligations for the analytical theorem.

## Issue classification and remaining obligations

No actual manuscript issue is classified as fatal, a demonstrated proof gap, or a missing essential assumption by this audit. The analytical counterexamples above concern two explicitly disclaimed stronger claims and show why the exact function-space and ordered-limit distinctions are essential. Mesh sensitivity is a limitation of numerical evidence, correctly acknowledged in the paper, rather than a theorem failure.

Every Maxwell result here remains an ordinary mathematical proof. This audit does not construct weak-Maxwell/Fourier foundations in Lean, prove the continuum localization theorem in the kernel, or infer novelty from an unsuccessful counterexample search. Separate statement correspondence, actual Lean source inspection, and a clean axiom audit remain necessary. The reported prior 692-theorem or 43-theorem counts receive no credit from this audit alone. Manuscript source archives, independent human review, complete prior-art comparison, and certified numerical continuum error bounds remain separate tasks.
