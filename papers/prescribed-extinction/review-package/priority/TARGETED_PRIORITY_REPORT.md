# Targeted theorem-level priority investigation

Date: 13 October 2026. Scope: the final prescribed-extinction compact Maxwell theorem, not a general investigation of OQ7.

**Verdict:** The inspected primary results establish much of the mechanism and several necessary bounds. They do not supply a verified derivation of the complete quantified theorem. The most defensible candidate contribution is the compact localization result uniform after removal of the vanishing physical-coupling factor, combined with exact extinction tuning and strictly positive capped tensor loss. **First priority remains unresolved**, especially against the unrecovered full Mann–Alù contribution and Gao–Yang–Kattawar paper. This is a bounded comparison of specified references, not an exhaustive priority determination.

The completed final-commit proof and audit are accepted as existing evidence. This investigation neither reopens F1–F4 nor infers novelty from Lean verification. It does not certify every intermediate statement in the reorganized manuscript.

## 1. The statement being compared

The recovered repository is at commit `686402a6c2d63820828729cc7ab02504632e3fe7`. Its declaration is
`OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement`.
The audited October 11 Theorem 1.1/Lemma 1.2 correspond to the release manuscript's Theorem 4.1/Lemma 4.2. Input hashes are in SOURCE_REGISTRY.md.

For each fixed $k>0,P>1,Q>0,E_*>0$, and every $0<\epsilon<1$, there is a finite two-layer square-aperture body in vacuum with:

- the same geometry and the same two material tensors for both illuminations;
- opposite propagation along $\pm e_z$, with the same real $e_y$ electric polarization and unit electric amplitude;
- local reciprocal anisotropic permittivities and $\mu=I$, satisfying
  $I\preceq\operatorname{Re}_H\varepsilon\preceq PI$ and
  $0\prec\operatorname{Im}_H\varepsilon\preceq QI$ in each layer;
- actual unique outgoing weak Maxwell solutions, physical absorption and all-angle scattering, including both transverse polarizations;
- exactly $X_+=X_-=E_*$, and
  $1-\epsilon<\Gamma=|A_+-A_-|/E_*=|S_+-S_-|/E_*<1$.

Thus the supremum of $\Gamma$ at that target is one; the supremum of the absorption difference is $E_*$; neither is attained.

Here $X,A,S$ are dimensional cross sections obtained by dividing powers by incident irradiance. They are not fractions of power incident on a selected aperture. “Same material” means that the object is unchanged under source reversal, not that its two layers have identical tensors. For complex polarization the reciprocal source generally involves conjugation; choosing real $e_y$ removes that ambiguity.

The quantifiers allow geometry and loss to vary with the accuracy and target. There is no common bound on aperture, thickness, volume, integrated resources, or positive loss floor across the sequence. This is a single-frequency theorem; it establishes neither bandwidth nor a fixed-resource optimum nor every interpretation of OQ7.

## 2. Primary evidence and access limits

The three tables in COMPARISON_MATRIX.md examine all nine requested criteria. SOURCE_REGISTRY.md identifies primary URLs, versions, page/equation locators, recovered PDF hashes, and incomplete access. “Unverified” in a limited-access row is an evidence gap, not a claim that a missing paper lacks a result.

**Mann–Alù 2023.** The official program and booklet announce optimized bianisotropic dipolar particles, opposite-direction extinction equality, maximal absorption from one side and zero absorption from the other. The booklet supplies the abstract, not the announced identities. The full contribution, equations and supplements were not recovered. Its critical-coupling wording does not determine $A/X$. [Official program](https://congress2023.metamorphose-vi.org/index.php/component/svisor/?Itemid=156&task=showScheduleSvisor), [booklet, PDF p.143](https://congress2023.metamorphose-vi.org/files/METAMATERIALS_2023_BOOKLET.pdf).

**Gao–Yang–Kattawar 2013.** Publisher previews identify extinction matrices for infinite and finite plates, normalization by projected area, analytical plane-wave formulas and ADDA comparisons of finite cylindrical plates. The reported agreement concerns large aspect ratio and small *incident* angles. Full Sections 4–6, equations and possible error statements were not recovered. The internal material-axis angle in the present construction is a different parameter. [Publisher evidence](https://www.sciencedirect.com/science/article/pii/S0022407313001064).

**Sounas–Alù.** The 2014 primary abstract states opposite-incidence extinction equality for the same polarization and permits asymmetric absorption/scattering. Full equations remain inaccessible. The complete 2017 accepted manuscript was recovered: its lossless two-port Eq. (1) is followed by multiport bounds, a stated extension to loss through additional channels, and the free-space extinction/gain bound Eq. (3). Describing the entire 2017 paper as merely lossless would omit relevant evidence. Its separately referenced supplemental derivations were not recovered. [2014 abstract](https://www.wip.osapublishing.org/ol/abstract.cfm?uri=ol-39-13-4053), [2017 accepted manuscript](https://link.aps.org/accepted/10.1103/PhysRevLett.118.154302).

**Other direct precedents.** Armitage's Jones analysis and Khurgin et al.'s selective attenuation establish reciprocal polarization/mode asymmetry. Their transmitted-channel amplitudes are not, without further work, compact-object absorption divided by extinction. [Armitage, Eq. (34)](https://arxiv.org/pdf/1311.5556), [Khurgin et al., published author copy, Sections 2–4](https://uriellevy.huji.ac.il/sites/default/files/uriellevy/files/emulating_exceptional-point_encirclements_using_imperfect_eaky_photonic_components_asymmetric_mode-switching_and_omni-polarizer_action.pdf).

Hopkins et al. provide an especially relevant compact precedent: a finite-volume electric-current formulation, common extinction, and opposite-incidence absorption/scattering simulations for stacked gold nanocrosses. The title's “nonreciprocal” response does not mean the underlying material breaks Lorentz reciprocity. Neither their plots nor their modal mechanism demonstrate the quantified capped-dielectric supremum at every exact target. [Published paper, Eq. (5), Section 3 and Fig. 3](https://mdpi-res.com/d_attachment/photonics/photonics-02-00745/article_deploy/photonics-02-00745.pdf).

Andersen–Frandsen use total-scattering absorption efficiency $A/(A+S)$, allow an upper envelope approaching one, and give a 93% matched-array example without its network realization. [Published paper, pp.2844–2846, Eqs. (7)–(22)](https://vbn.aau.dk/ws/files/19704710/Absorption_Efficiency.pdf).

The recovered reciprocal sheet treatment of Ra'di et al., the reciprocal polarizer subsystem in Kononchuk et al., and the 2026 dielectric-metasurface TCMT treatment are relevant opposite-side precedents. The complete Kononchuk isolator includes magnetic nonreciprocity and must be separated from its reciprocal polarizer. The 2026 full publisher prose was read, but equation rendering, PDF and supplement access were incomplete; no missing Eq. (17) formula is reconstructed here. Yazdi et al.'s full article remains an access gap. [Ra'di et al., Section II and conclusion](https://arxiv.org/pdf/1211.3549), [Kononchuk et al., Sections II–III](https://arxiv.org/pdf/1903.01507), [Máñez-Espina et al., Sections 3–4](https://onlinelibrary.wiley.com/doi/full/10.1002/nap2.70145), [Yazdi institutional record](https://research.aalto.fi/en/publications/a-bianisotropic-metasurface-with-resonant-asymmetric-absorption/).

## 3. Derivation attempts and their first unsupported implications

The following are logical comparisons performed here. A missing implication means that the inspected evidence does not justify that inference; it is not a proof that no other derivation exists.

### 3.1 Reciprocity and energy conservation

Grant $X_+=X_-=X>0$ and $A_\pm+S_\pm=X$, with nonnegative powers. Immediately,
$$
 |A_+-A_-|=|S_+-S_-|\le X.
$$
For a compact body with continuous far field and the forward optical theorem, equality would force one scattering power to vanish. Its far field then vanishes everywhere, including forward, forcing $X=0$. Hence the strict inequality for an individual object is an immediate consequence of standard identities.

**First gap:** these identities give an upper bound and nonattainment, not a family approaching the bound at a prescribed $E_*$. The elementary inference supplies no priority basis for the existence theorem.

### 3.2 Optimal dipolar response

Grant the Mann–Alù announced zero reverse absorption. Then
$$
 \Gamma=A_+/X=A_+/(A_++S_+).
$$
Maximizing $A_+$ is a different optimization from making this ratio approach one. To complete that step requires the actual optimality identities and their normalization. **This first step is access-limited.** Neither $1/2$ nor one is assigned to the ratio from critical coupling alone.

Even if that step were granted, one would still need a realization theorem for local $\mu=I$ dielectric volumes under every prescribed $P>1,Q>0$, with the same object for both sources and every exact $E_*>0$ at fixed $k$. An optimized polarizability tensor is not such a realization theorem. Scaling incident amplitude cannot fix a normalized cross section; scaling frequency changes the problem. Combining particles would require control of their interactions and all scattered radiation.

### 3.3 Antenna efficiency and time-reversal bounds

Write $\eta_\pm=A_\pm/X$. Then $\Gamma=|\eta_+-\eta_-|$. An efficiency envelope allowing $\eta_+\to1$ does not construct a single object for which $\eta_-\to0$, nor prove attainability of that envelope.

For the matched-antenna assumptions, Andersen–Frandsen's Eq. (22) is
$$
 \tfrac12(1-\sqrt{1-D_a/D_s})\le\eta\le
 \tfrac12(1+\sqrt{1-D_a/D_s}).
$$
Here $D_a$ looks toward the source and $D_s$ is the scattering directivity forward. The ratio is unchanged by their wavelength normalization. This gives a necessary efficiency/directivity constraint, not the required two-source dielectric construction. [Primary Eq. (22)](https://vbn.aau.dk/ws/files/19704710/Absorption_Efficiency.pdf).

Sounas–Alù 2017 also constrain admissible responses: Eq. (2) relates port-emission efficiencies to interport transmission, and Eq. (3) relates directional emitter gain to extinction. **First gap in both routes:** a necessary inequality is not an existence/attainability statement for the two physical plane-wave experiments. The local-material and exact-target requirements remain additional obligations. [Primary Eqs. (2)–(3)](https://link.aps.org/accepted/10.1103/PhysRevLett.118.154302).

Schab et al. retain total radiation and derive current-optimization bounds by relaxing the full driven integral equation to power constraints. **First gap:** an extremizing relaxed current need not be the actual pair of Maxwell currents induced by the two sources in one capped two-layer object. Their “prescribed losses/materials” terminology does not mean exactly prescribed extinction. [Schab et al., Section 2, Eqs. (2), (6), (8)](https://arxiv.org/pdf/2009.08502).

### 3.4 The strongest planar route

The most promising synthesis begins with the known polarization/selective-loss mechanism and the established periodic optical theorem. Gustafsson et al.'s Eq. (2.6) gives
$$
 \sigma_{\mathrm{ext}}=2\mathcal A\operatorname{Re}(1-T),
$$
where $\mathcal A$ is cell area and $T$ is the co-polarized transmission with the vacuum reference phase removed. The derivation includes the other propagating modes in the power balance. It does not identify extinction with $1-|T|^2$. [Gustafsson et al., report pp.3–4, Eq. (2.6)](https://lup.lub.lu.se/search/files/96358663/TEAT_7213.pdf).

The following algebra is our reconstruction of the manuscript's ideal planar family, not an equation attributed to Mann, Gao, or Armitage. A reflectionless half-wave plate with axis $u_\theta=\cos\theta e_x+\sin\theta e_y$ precedes or follows an $x$-selective absorber. For the same $y$ incidence, the vacuum-referenced co-polar transmission is $\cos2\theta$; the absorption from the plate side is $A_x\sin^22\theta$, and from the absorber side it is zero. Thus the planar densities are
$$
 x_\infty=4\sin^2\theta,\qquad
 a_\infty^+=0,\qquad
 a_\infty^-=A_x\sin^22\theta,\qquad
 \gamma_\infty=A_x\cos^2\theta.
$$
These formulas include reflected and converted channels through the optical power identities; transmission alone is insufficient.

The ordinary slab adaptation to arbitrary upper caps is explicit: choose
$p_j=(2j/(2j-1))^2\le P$, $kd=(2j-1)\pi$, so the active-axis phase is $2j\pi$ and the orthogonal-axis phase is $(2j-1)\pi$. A weakly lossy $x$ absorber with permittivity $1+i\eta$, small $\eta\le Q$ and sufficiently large finite thickness has small reflection and transmission, so $A_x\to1$. Slab matching and this limit are routine adaptations of established optics; the ideal tensors still have loss-free directions and the geometry is transversely infinite.

**First unsupported bridge after this planar synthesis:** converting it into literal sharp compact material truncations, with current and physical-power estimates uniform *after factoring out* the vanishing source coupling. A fixed-angle finite-to-planar limit does not establish this bridge.

### 3.5 Why the uniformity has mathematical content

In the intermediate rank-one family, the *material axis* rotates while incident amplitude is fixed:
$$
 p_{R,\theta}=\sin\theta\,J_\theta r_{R,\theta},\qquad
 X_{R,\theta}=\sin^2\theta\,Y_R(\theta).
$$
The needed bridge is a limit such as
$$
 \sup_{\theta\in I}\left|Y_R(\theta)/R^2-Y_\infty(\theta)\right|\to0,
$$
and analogous normalized absorption and all-channel scattering limits, on an interval $I$ containing zero. The normalized auxiliary drive exists at zero even though the physical current there vanishes.

Holding $X=E_*$ makes the selected angle of order $R^{-1}$. Therefore an absolute error small compared with a fixed planar density may be large compared with the selected density of order $R^{-2}$.

For a purely logical illustration, take dimensionless $r\to\infty$, $\phi(t)=t^2/(1+t^2)$, and
$$
 q_r(\theta)=4\theta^2+r^{-1}\phi(r\theta).
$$
This has $q_r(0)=0$ and uniformly vanishing absolute density error $\le r^{-1}$. Yet at $\theta=c/r$, $r^2(q_r-4\theta^2)=r\phi(c)$, which diverges. This is not a Maxwell counterexample; it demonstrates that the proposed inference from absolute convergence to relative convergence is invalid.

The WGF sources deserve their strongest reading: Bruno et al.'s inspected preprint gives a superalgebraic window-error argument and an analytic flat-background correction, rather than only plots. Arrieta–Pérez-Arancibia state superalgebraic central-region current approximation for 3D electromagnetic surface equations and separately test discretization convergence. Their computational windows retain the physical layered background. They do not perform the present sharp volumetric material truncation. Control of external grazing incidence is not control of the internal material-axis coupling. [Bruno et al., 2015 preprint PDF pp.4–6, Eqs. (6)–(10)](https://arxiv.org/pdf/1507.04445), [Arrieta–Pérez-Arancibia, Section V, PDF pp.4–5](https://arxiv.org/pdf/2210.02565).

The distinct 28-page published Bruno paper and its ZIP supplement were located but normal retrieval was blocked. The published abstract announces near- and far-field window accuracy; that claim is granted here, while final additions and detailed derivations remain unread. [Published-version repository record](https://authors.library.caltech.edu/records/w3sjb-41r38), [publisher supplement record](https://epubs.siam.org/doi/10.1137/15M1033782).

Even granting all those window estimates, transferring them requires a new equivalence/stability argument for this physical truncation, normalization, global current norm and radiation power. A citation to WGF alone does not discharge that obligation. Gao's accessible numerical finite-plate comparison also does not discharge it; the full-paper equivalence question remains open.

This normalized estimate is a sufficient bridge used by this proof route. It is not asserted to be a necessary form of every conceivable proof of the final theorem.

### 3.6 What follows once the bridge is granted

If $Y_\infty(0)>0$, choose constants $a<b$ with
$a^2Y_\infty(0)<E_*<b^2Y_\infty(0)$.
Uniform normalized convergence gives, for sufficiently large finite $R$,
$$
 X_{R,a/R}<E_*<X_{R,b/R}.
$$
Continuity and the intermediate-value theorem then give an *exact* target inside that bracket, while the normalized ratio stays near its planar value.

For that fixed finite body, small positive isotropic loss $i\nu I$ can then be added to both tensors, with slack below $Q$. A bounded inverse and a Neumann perturbation argument preserve the strict target bracket and the ratio; a second intermediate-value argument restores exact extinction. These are routine functional-analytic consequences once their physical hypotheses are established.

The order matters: absorber and active plate loss are fixed before the aperture limit; isotropic regularization comes after selection of a finite body. No uniform estimate as all active losses vanish or thicknesses diverge is inferred.

## 4. Classification of the contribution

| Category | Assessment |
|---|---|
| Already-known ingredients | Reciprocal extinction equality; different absorption/scattering under reversal; Jones transpose constraints; polarization conversion with selective loss; planar optical theorem; efficiency/directivity obstruction; windowed layered-media methods. Compact examples also precede this work. |
| Immediate corollaries | Passive bound, equality of absorption and scattering differences, and compact strict nonattainment from continuous far field plus optical theorem; exact suprema once a near-unit prescribed-target sequence exists. |
| Routine adaptations, conditional on hypotheses | Half-wave phase matching below any real-permittivity cap by increasing thickness; weak-loss/thick-absorber limit; continuity and intermediate-value tuning; Neumann stability for a selected finite body. These should not be sold separately as new physical mechanisms. |
| Potentially distinct theorem | Uniform physical finite-aperture localization for normalized auxiliary currents and all physical powers at vanishing material coupling, sufficient to realize every exact positive extinction in the capped strictly lossy compact dielectric class. The complete combination, not its familiar ingredients, is the candidate. |
| Unresolved access/equivalence | Full Mann–Alù optimality identities and realizability scope; full Gao equations/error estimates; full Yazdi article; Sounas 2014 equations and 2017 supplement; typeset 2026 equations/supplement; final Bruno PDF and supplement. |
| External judgment still needed | Whether the missing bridge is an established result under another formulation, or a routine application of a known uniform localization theorem; whether an older alternative construction yields the same quantifiers. |

## 5. Internal versions and the limits of this verdict

The project's October 10 compact variable-extinction manuscript, October 11 prescribed-extinction manuscript, frozen Lean source, and later publication manuscript are **our own unpublished materials**, not independent external prior art. Their overlap is internal chronology. Neither filenames nor timestamps establish public disclosure or independent priority. The older scalar checkpoint and finite-port package are not substitutes for the final full-Maxwell theorem.

The completed final audit concerns proof validity and main-statement correspondence. It supplies no literature-priority conclusion. This run supplies an AI-assisted, source-checked comparison, not human peer review, an independently implemented kernel check, or a new audit of all manuscript proofs.

A safe contribution statement is supplied separately. The access drafts have not been sent. No manuscript, frozen source, historical original, or prior release was modified. No publication, submission, or contact occurred.

**Precise disposition:** qualitative phenomenon and main ingredients — prior art established; complete-theorem derivation from inspected results — not established; candidate distinction — identified at the normalized compact localization/exact-target combination; first or exclusive novelty — not established; priority review — incomplete pending the specifically identified primary-access and expert-equivalence questions.

