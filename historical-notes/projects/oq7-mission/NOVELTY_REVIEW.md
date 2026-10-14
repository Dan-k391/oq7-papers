# OQ7 prior-art and equivalence review

Independent review, 10 October 2026. The objects of comparison are the supplied 41-page Paper A and 24-page Paper B dated 10 October 2026. This report assesses originality separately from mathematical correctness and kernel verification. It does not establish priority. An unsuccessful search, an author assertion, or a Lean proof cannot establish novelty.

## Assessment

Reciprocal extinction equality, directional absorption with compensating directional scattering, radiation-dressed dipole passivity, and polarizer–waveplate directional effects have substantial prior art. The scalar two-port feasible region is already covered by Guo–Fan. These should be treated as foundations or explicit corollaries.

The strongest potentially distinctive part of Paper B is the combination of its **physical material-truncation theorem for a fixed strictly absorbing tensor stack** with its **two-layer compact construction under arbitrarily prescribed upper material caps**. The unrestricted ratio approaching one, considered without that local-material realization, is insufficiently distinctive: receiving-antenna efficiency can already approach one, and Mann–Alù explicitly announced maximal directional dipole absorption in 2023. The prior results below do not, from the retrieved material, supply Paper B's exact compact capped-dielectric theorem. That is a comparison of statements, not a claim that no equivalent theorem exists.

Paper A's exact restricted thickness asymptotic and its full prescribed-overlap three-branch matrix boundary are reasonable candidates for further priority assessment. Weighted observability, sinusoidal concentration, numerical ranges, contraction geometry, and quantum-state discrimination substantially precede their components. The complete coefficient and physical matching construction in A5.1, and the complete feasible optimization in A7.1, need to be compared rather than advertised as new applications of unfamiliar terminology.

## Exact OQ7 scope

The supplied tutorial was checked directly at PDF pages 70–71 in `extracted/Tutorial.json`. It states reciprocal extinction equality for time-reversed incident fields and asks broadly for bounds on absorption–scattering asymmetry. It does not prescribe Paper B's normalization, a compact dielectric class, common geometric resources, or common positive loss. Paper B addresses one explicitly specified resource-unrestricted, single-frequency compact supremum; it does not settle every constrained, broadband, or fixed-size interpretation of the question. [Miller–Monticone, tutorial, §4.1, pp. 70–71](https://arxiv.org/abs/2605.24738v1).

## Source-by-source comparison

### 1. Sounas–Alù: extinction symmetry, 2014

The publisher abstract establishes opposite-direction extinction equality for reciprocal objects and explains why absorption permits directional scattering differences. This anticipates the basic premise of both manuscripts. It supplies neither the sharp resource-restricted thickness coefficient nor the asserted physical aperture limit. The abstract's polarization wording should be read with the actual time-reversed pair, including conjugation for complex polarization. The publisher's linked full-article and PDF endpoints did not expose readable article content in this review; a complete equation comparison remains open. [Optics Letters 39, 4053–4056, DOI 10.1364/OL.39.004053](https://opg.optica.org/ol/abstract.cfm?uri=ol-39-13-4053).

### 2. Sounas–Alù: time-reversal bounds, 2017

The accepted full manuscript derives internal-field asymmetry bounds first for lossless two-port systems, then for multiple ports and free-space objects. Its two-port bound depends on reflection/transmission and forces equal internal intensities at perfect transmission. These are substantive precedents for asymmetry constraints. A finite absorbing structure is not itself time-reversal invariant; reciprocity alone does not license importing the lossless internal-field proof into the exact lossy assertions here. [Accepted manuscript, PRL 118, 154302, especially Eq. (1)](https://link.aps.org/accepted/10.1103/PhysRevLett.118.154302).

### 3. Hopkins et al.: modal directional absorption, 2015

The primary article describes opposite-direction absorption and scattering differences at equal extinction, attributes them to nonorthogonal eigenmodes and modal interference, and gives a stacked nanocross design. Thus directional absorption in reciprocal three-dimensional particles, and nonnormal/modal-interference explanations, are established subjects. This is not an equivalent proof of a unit normalized compact supremum under fixed positive dielectric caps. The publisher's indexed article text, introduction and conclusion were available; direct page opening intermittently failed. [Photonics 2, 745–757](https://www.mdpi.com/2304-6732/2/2/745).

### 4. Mann–Alù: maximum asymmetric dipole absorption, 2023

The official conference program places **“Maximum Asymmetric Absorption and Scattering in Bianisotropic Particles”** on 14 September 2023, 11:15–11:30. Its abstract explicitly describes optimal bianisotropy for dipoles, critical coupling from one side with maximal absorption, zero absorption from the opposite side, and identities for that response. This is direct prior art for Paper B2's qualitative extremal dipole phenomenon. Full equations, normalization and tensor family were not retrieved, so equivalence to B2.1's exact curve and equality family remains unresolved. [Official Metamaterials 2023 program](https://congress2023.metamorphose-vi.org/index.php/component/svisor/?Itemid=156&task=showScheduleSvisor).

### 5. Andersen–Frandsen: receiving-antenna absorption efficiency, 2005

The actual eight-page institutional PDF (cover plus published article) is accessible through an alternate university URL. It defines efficiency as absorbed power divided by absorbed plus total scattered power, obtains directivity-dependent optical-theorem bounds, and explicitly allows efficiency arbitrarily near one. Its assumptions include a lossless antenna connected to a matched absorbing load; examples include networked dipoles. Thus a blanket first claim for absorption/extinction approaching one would be untenable. It does not establish zero reverse absorption or Paper B's bounded local dielectric realization. Equation glyph extraction and page rendering were incomplete, so Eq. (22)'s exact symbolic comparison still needs visual checking. [University copy, IEEE TAP 53, 2843–2849](https://vbn.aau.dk/ws/files/19704710/Absorption_Efficiency.pdf).

The manuscript's statement that this complete paper was unavailable should be updated. The originally cited `/files/19704710/absorption_efficiency.pdf` endpoint and direct download attempts returned errors/HTTP 403 here; the alternate `/ws/files/` PDF was readable through the web service. No local literature PDF download was successfully saved.

### 6. Sersic et al.: full magnetoelectric dipole optical theorem, 2011

The complete preprint develops a 6×6 electric–magnetic polarizability, the extinction and integrated-radiation quadratic forms, and radiation damping. These are the necessary established foundations for Paper B2's radiation-consistent calculation; that consistency is not itself novel. Its later eigenpolarizability reduction explicitly uses orthogonal eigenvectors. The quadratic forms remain the appropriate comparison for a nonnormal tensor; an eigenvalue-only comparison would miss the distinction. The exact B2 two-illumination tradeoff should also be checked against Mann–Alù's missing identities. [Magnetoelectric point scattering theory for metamaterial scatterers, Eqs. (15)–(23)](https://arxiv.org/pdf/1012.3671).

### 7. Fleury–Soric–Alù: absorption–scattering tradeoffs, 2014

This complete preprint derives passive absorption/scattering tradeoffs by channel and discusses cloaked sensors, resonances, and transparency. A dipole extinction–absorption envelope obtained from the optical theorem and a quadratic radiation norm is closely connected to this established framework. Paper B's comparison should identify the precise additional simultaneous reciprocal-illumination restriction and equality family, after aligning channel and cross-section conventions. The older result alone does not assert the capped compact local dielectric construction. [Physical bounds on absorption and scattering for cloaked sensors, PRB 89, 045122](https://arxiv.org/pdf/1309.3619).

### 8. Guo–Fan: reciprocal reflection feasibility, 2022

The author-hosted published paper gives necessary and sufficient feasible diagonal reflection coefficients for matrices with prescribed singular values. Eqs. (24)–(28) include the two-port condition that the sum of reflection magnitudes is at least the singular-value difference. Paper A's scalar two-port bound and feasibility discussion are eliminations/slices of these known constraints, as Paper A acknowledges. A new plotted constant or convenient formula is not a new feasible-region theorem. [PRL 128, 256101, full published paper](https://cguo.org/pdf/guo2022b.pdf), [supplement](https://cguo.org/pdf/guo2022b_SI.pdf).

### 9. Guo–Fan: transmission/reflection/absorption eigenvalues, 2024

The full published paper's main theorem characterizes all joint eigenvalue tuples through a trace identity and Horn-type inequalities. This is broader abstract eigenvalue feasibility than a single absorption-asymmetry inequality. Paper A7 additionally fixes a coherent reference/forward extinction quantity and the overlap of two related incident states. Equivalence requires a reduction preserving those data; comparing only absorption eigenvalues is insufficient. The paper does not provide a local Maxwell realization for every feasible abstract tuple. [PRB 110, 205431, main theorem Eqs. (45)–(49)](https://cguo.org/pdf/guo2024f.pdf).

### 10. Li–Kim–Fan–Guo: joint coherent control, 2025

The full published article uses numerical ranges of power matrices to characterize achievable transmission, reflection and absorption for a fixed scattering system as the input is varied. Theorem 1, Eqs. (11)–(14), is a direct relevant matrix-optimization precedent. A7 instead optimizes the reciprocal contraction as well, while fixing a two-state overlap and coherent extinction. The two problems have different quantifiers. This distinction does not prove originality: A7 could still follow from a known constrained numerical-range or matrix-completion theorem. [PRB 112, 245421](https://cguo.org/pdf/li2025.pdf).

### 11. Lins–Spitkovsky–Zhong: normalized numerical range, 2017 preprint

This complete primary preprint connects the normalized numerical range to the Davis–Wielandt shell and gives detailed two-dimensional boundary descriptions. Its coordinates combine a quadratic forward amplitude with output norm, making it a useful equivalence candidate for coherent-extinction constraints. Its stated problem fixes a matrix and varies a vector; A7 varies a reciprocal contraction with a prescribed pair of inputs. No mapping carrying A7's complete three-branch boundary into this theorem has been established here. [The normalized numerical range and the Davis–Wielandt shell](https://arxiv.org/pdf/1712.01070).

### 12. Quantum two-state discrimination and transformation

Buscemi–Sacchi optimize average discrimination success against average post-measurement fidelity for a complete two-outcome quantum instrument. Eq. (25) is an explicit tradeoff. Paper A7 fixes coherent forward amplitude of a single scattering contraction, rather than the disturbance of an outcome-discarded quantum instrument. The objective and feasible maps differ. [PRA 74, 052320, Eqs. (1)–(3), (25)](https://arxiv.org/pdf/quant-ph/0610196).

D'Ariano et al. optimize minimum success probability and minimum fidelity to prescribed target states; Eqs. (12)–(13) and (26) specify that boundary. The pair-transformation geometry and contraction/dilation tools are relevant, but these objectives do not identify A7's boundary. A concrete change of variables and feasible-set correspondence would be needed to claim equivalence. [Probability-fidelity tradeoffs for targeted quantum operations](https://arxiv.org/pdf/0902.0695).

### 13. Observability and capped sinusoidal concentration

Chitour–Sigalotti's Lemma 2.5 gives uniform positive weighted Gramian floors for fixed collections of oscillators and persistently exciting measurable weights. This anticipates the principle of an observation/loss floor. Its fixed generator does not itself control every varying physical dielectric profile or supply A5.1's sharp coefficient. [On the stabilization of persistently excited linear systems, Lemma 2.5](https://arxiv.org/pdf/0810.2122).

Hante–Sigalotti–Tucsnak's Proposition 5.4 gives a quantitative short-interval weighted observability lower bound for a fixed skew-symmetric controllable pair, with power determined by its controllability index. This is a concrete precedent for the local polynomial scaling mechanism, rather than merely a related title. [On conditions for asymptotic stability…, Proposition 5.4](https://arxiv.org/pdf/1108.4327).

Privat–Trélat–Zuazua's Remark 2 bounds the integral of sine squared over a measurable set of fixed measure using the expression containing `Lπ − sin(Lπ)`. Its small-measure cubic behavior directly precedes the capped sinusoidal moment ingredient. The author-hosted preprint's indexed primary text was available; direct PDF opening failed. A5's passage to exact finite-loss physical constraints, its global lower coefficient and matched construction require additional work. [Optimal observation of the one-dimensional wave equation, Remark 2](https://w3.ens-rennes.fr/math/people/yannick.privat/documents/optimobswave.pdf).

### 14. Ma–Pestourie–Johnson: field and weak-loss bounds, 2025

The complete preprint strengthens lossless internal-field bounds and derives a first-order weak-loss bound on asymmetry of two-port reflectances normalized by total loss. Section VII, Eq. (35), explicitly contains an error term and a lossless-background reflection coefficient. It is relevant prior art for finite-loss asymmetry questions, but it is not an exact finite-loss bound with the identical fixed budgets of A5. The distinction should be the hypotheses and error term, rather than calling all time-reversal bounds inapplicable. [PRA 111, 063518, §VII](https://arxiv.org/pdf/2503.03342).

### 15. Armitage: reciprocal Jones matrices, 2014

The full preprint gives forward/backward transposition constraints and an explicit linear polarizer–quarter-wave-plate composite at 45 degrees, with nonnormal transmission and direction-dependent output polarization. It is direct prior art for the polarization-conversion mechanism. Paper A6/B3's physical work must be framed as exact dielectric implementation, matching, material caps, loss regularization and compact localization, rather than discovery of the polarizer–waveplate idea. [PRB 90, 035135, Eqs. (27), (34)](https://arxiv.org/pdf/1311.5556).

### 16. Gao–Yang–Kattawar: finite plates, 2013

The primary publisher preview derives infinite-plate extinction analytically, relates plane-wave and spherical-wave extinction formalisms, and compares finite cylindrical plates using DDA against infinite-radius plates. Section 6 is expressly described as numerical convergence testing; agreement is reported for large aspect ratios and small incident angles. This is strong prior art for the finite-to-planar limit and prevents describing that physical expectation as new. The complete article was not retrieved. The available preview does not supply B3.1's tensor hypotheses, strictly positive fixed-loss inverse estimate, proof in current norm, or all-cross-section limit. [JQSRT 131, 72–81, DOI 10.1016/j.jqsrt.2013.03.010](https://www.sciencedirect.com/science/article/pii/S0022407313001064).

### 17. Mathematical volume-integral theory

Yurkin–Mishchenko's complete 2018 paper derives the electric VIE from Maxwell equations, interface conditions, radiation and local energy, explicitly treating the singular kernel for finite isotropic multilayer particles with edges and corners. Its conclusion discusses extension to anisotropy and unresolved general existence/continuity conditions. This is established analytical infrastructure, not an aperture theorem. B3 must justify its own tensor formulation and size-uniform fixed-loss estimate; citing this isotropic result alone does not prove those steps. [PRA 97, 043824, §§II–VII and conclusion](https://www.scattering.ru/papers/Yurkin%20and%20Mishchenko%20-%202018%20-%20Volume%20integral%20equation%20for%20electromagnetic%20scatt.pdf).

The associated primary tutorial treats impressed fields, dyadic reciprocity and VIE identities. It is useful for convention and formulation checks, while its explicit material class is isotropic. [Impressed sources and fields in the volume-integral-equation formulation…, JQSRT 2018](https://pmc.ncbi.nlm.nih.gov/articles/PMC6074055/).

### 18. Windowed Green functions and large-aperture localization

Bruno–Lyon–Pérez-Arancibia–Turc develop smooth-window integral equations for scattering at infinite layered interfaces, with planar-background corrections and rapidly convergent numerical near/far fields. This anticipates smooth windowing and careful treatment of shallow incidence. Its target is the original infinite-interface problem, not a physically cut-off material body whose normalized cross sections approach a planar density. [Windowed Green function method for layered-media scattering](https://arxiv.org/pdf/1507.04445).

Arrieta–Pérez-Arancibia give a three-dimensional Maxwell second-kind surface formulation. Eqs. (21)–(23) window the integral kernels to approximate currents on an infinite interface; §V separately explains far-field recovery. Those statements differ from B3.1's literal `χ_R = 1_(RΩ) χ(z)`, full-sphere radiated power and optical identity. The numerical method's super-algebraic window error cannot be substituted for B's physical aperture error. [Windowed Green function MoM…, IEEE TAP 2022, §V](https://arxiv.org/pdf/2210.02565).

### 19. Other unresolved or model-restricted comparisons

Martin's 1962 primary publisher summary states inequalities between total, absorption and elastic cross sections when the imaginary potential's range is not too small relative to the real potential's range. Full subscription text was not retrieved. Its assumptions and constants must be checked before ruling it equivalent or unrelated to any finite-resource lower bound. The article's issue date is February 1962; the webpage's 2008 date is not scientific priority. [Some simple inequalities in scattering by complex potentials](https://link.springer.com/article/10.1007/BF02733216).

Máñez-Espina et al.'s 2026 primary article uses a coupled-resonance model to optimize directional absorption difference and explains its dependence on background reflection. This further establishes the maximum-directional-absorption design theme. A two-mode TCMT result and its simulated dielectric metasurface do not automatically establish B's general exact compact continuum theorem. Readable publisher indexed text including Eq. (17)'s discussion was available; equation rendering and the complete supporting information were not inspected. [Strong mode coupling and maximum directional absorption…, DOI 10.1002/nap2.70145](https://onlinelibrary.wiley.com/doi/10.1002/nap2.70145).

## Equivalence tests and dispositions

These are reviewer inferences from the supplied definitions and the primary statements above.

| Manuscript assertion | Required equivalence test | Present disposition |
|---|---|---|
| Reciprocal extinction equality | Same time-reversed fields, sign convention and normalization | Established foundation; no independent novelty claim |
| A6.3 scalar two-port bound | Eliminate reflection/singular-value variables from the known feasible region | Corollary of existing matrix feasibility |
| A6.2 channel envelope; B2 dipole envelope | Align radiation norm, channels, extinction and two reciprocal inputs with passive quadratic/channel bounds | Simple upper-bound structure is established; exact two-input equality family needs Mann–Alù equations |
| A6.4/B planar polarization construction | Compare reciprocal Jones mechanism, then exact local dielectric and matching requirements | Mechanism established; precise implementation can still contribute |
| A7.1 | Map coherent forward extinction and two-state overlap into known numerical-range, contraction or quantum-instrument feasible sets, preserving sharpness and dimensions | Known plateau/geometry ingredients; exact middle branch priority unresolved |
| A4.5/A5.1 | Compare weighted Gramian floors and sine concentration, then retain varying dielectric dynamics and exact physical budgets | Underlying principles established; sharp restricted coefficient plus matching remains a plausible specific advance |
| B3.1/B3.8 | Physical tensor material truncation versus computational kernel truncation; fixed loss; area normalization; all scattering angles; constants and aperture rate | A substantive precise distinction; no complete equivalence identified in retrieved sources |
| B1.1/B3.11 | Same fixed `k, P>1, Q>0`, local nonmagnetic dielectric class, regular finite objects, exact Maxwell cross sections and resource-unrestricted sequence | Plausibly distinctive realization theorem; abstract/antenna unit efficiency alone is already known |

For A7's plateau, the optimization of the expectation difference of a positive contraction on two pure states is the familiar two-state trace-distance calculation. For the outer branch, the basic contraction/forward-amplitude disk already yields the parabolic bound. The originality question is consequently the additional joint constraint, the middle branch, transitions, and complete sharp realization in the abstract class. A formal positive-matrix certificate alone cannot establish originality of that optimization.

For B's cap construction, enlarging dimensions while weakening individual loss does not preserve a common positive lower loss or geometric resource. The fixed-loss hypothesis is used separately for each aperture limit. This distinction is central both to correctness and to prior-art comparison: the theorem should not be promoted as a fixed-size or uniformly lossy performance bound.

## What remains before a publication-level originality claim

1. Obtain Mann–Alù's complete 2023 proceedings contribution or author-provided equations, and compare B2.1 after exact normalization and reciprocity conventions.
2. Obtain Gao et al.'s full 2013 article and the complete Martin paper. Verify mathematical statements rather than infer their absence from previews.
3. Visually check Andersen–Frandsen Eq. (22) from the accessible institutional PDF; replace the manuscript's access-limitation claim with its substantive comparison.
4. Test A7 against constrained numerical-range and contraction-completion results with an explicit feasible-set mapping. Different physical terminology and different optimization variables alone are not a priority argument.
5. Broaden the exact B3.1 comparison to rigorous large dielectric-screen/plate asymptotics, including diffraction and integrated-power limits; the present targeted review is not exhaustive.
6. State contributions at the level of the exact theorem. Cite known mechanisms and inherited inequalities. Treat scientific novelty, ordinary proof validation and Lean certification as separate claims.

No evidence in this review licenses a definitive “first” claim. The narrow physical localization and capped compact realization results are **plausible candidates**, conditional on their mathematical audit and the unresolved exact prior-art comparisons.
