**Status: blocked before kernel verification.** This checkpoint records the exact target from the OQ7 paper, the remaining proof obligations, and ordinary mathematical proof adaptations checked during the audit on 9 October 2026. It is not a compiled Lean project. No OQ7 theorem was accepted by Lean in this turn; no `lake build` or `#print axioms` command could be executed.

## Exact target

Source: `OQ7_verified_research_note.pdf`, Theorem 5.1 on page 10, with its proof on pages 10–13 and the lower-bound lemmas on pages 6–9.

Fix k > 0, P > 1, Q > 0, M > 0, 0 < T < 1, and 0 < a < (1 − T²)/2. The physical class consists of finite homogeneous dielectric multilayers at normal incidence, with relative permeability one, scalar permittivity p + iq, identical vacuum exterior media, 1 ≤ p ≤ P, 0 ≤ q ≤ Q, integrated loss exactly M, transmitted power exactly T, and mean absorptance exactly a. Total thickness includes all spacers and matching layers. There is no positive minimum layer width or fixed material catalogue.

Define

```text
b = 1 − T − a
s = √(1 − 2a)
y₀ = s − T
x₀ = √(b² − y₀²)
D₀ = 2x₀
α = T y₀ / (s x₀)
C_L = the physical exact-target class with total thickness ≤ L
D*(L) = sup { |A_L − A_R| : stack ∈ C_L }, when C_L is nonempty
```

The theorem asserts eventual nonemptiness of C_L, strict D < D₀ for every finite admissible stack, and

```text
lim as L → ∞ of (kL)² [D₀ − D*(L)] = α π² (kM)⁴ / (3 P Q²).
```

None of these hypotheses or conclusions may be replaced by an assumed abstract response model or by approximate target matching.

## Execution blocker

The environment supplied with the request reports:

```text
409 Conflict, environment_offline
Environment is not connected.
```

The workspace is `/workspace/scratch/454ecf1f116b`. The available tools expose no shell, Lean runner, general command executor, or supported environment-reconnection action. Consequently no Lean version, pinned Mathlib checkout, build, or axiom report was verified in this turn. The earlier unexecuted algebra draft remains unverified.

A connected Linux or WSL2 execution environment is required before compilation can start. No permissions change or unsafe runtime workaround was attempted.

## Verification ledger

| Result | Work still required | Kernel status |
| - | - | - |
| Two-port model and determinant identities | Define the actual complex matrix S, passivity, absorptances, transfer conversion, and prove the identities from these definitions | Unverified |
| Maxwell and Gram identities | Construct fields from finite layers; prove interface regularity, scattering existence, nonzero transmission, flux balance, Wronskian identity, and the Gram determinant integral | Unverified |
| Lemma 4.1 | Complex Helmholtz modulus comparison with interface and endpoint control | Unverified |
| Lemma 4.2 | Capped Fourier moment, including zero mass and full-period mass | Unverified |
| Lemma 4.3 | Cell bound, Hermitian PSD determinant Minkowski inequality, and finite aggregation | Unverified |
| Lemma 4.4 | Convexity on the half period, endpoint regularity, and a separate supporting tangent on the full period | Unverified |
| Theorem 4.5 | Partition accounting, finite positive floor, and uniform asymptotic lower bound over varying physical stacks | Unverified |
| Section 5 construction | Exact layer transfer matrices, material and thickness accounting, and a proved matrix remainder | Unverified |
| Section 5 exact matching | Smooth physical response, invertible real derivative, implicit matching, and ordinary dielectric realization | Unverified |
| Theorem 5.1 | Eventual nonemptiness, bounded supremum, all-budget construction, and the final squeeze | Unverified |

Independent mathematical review found no fatal error in the audited theorem under the manuscript’s finite piecewise constant model. That assessment is separate from kernel verification.

## Helmholtz comparison without Poincare

The following reorganization preserves Lemma 4.1 and removes the need to formalize sharp Dirichlet Poincaré or a Taylor expansion at the initial zero.

Translate the initial point to zero. Let s(0) = 0, s′(0) = 1, ρ = |s|, and K = k√P. Initial differentiability gives ρ > 0 on a sufficiently small right neighborhood. If a zero occurs before π/K, continuity and compactness give a first zero h₀ in that interval.

On 0 < h < h₀, the modulus is differentiable and the equation gives

```text
ρ″ + K²ρ = (K² − k²p)ρ + j²/ρ³ ≥ 0,
j = Im(conj(s) s′).
```

For 0 < δ < h < h₀, variation of constants on the interval away from zero yields

```text
ρ(h) ≥ ρ(δ) cos(K(h − δ)) + ρ′(δ) sin(K(h − δ))/K.
```

The omitted forcing integral is nonnegative because its sine kernel is nonnegative. The field and its first derivative are continuous across interfaces, so the piecewise formula has no interface jump terms. From s(δ)/δ → 1 and s′(δ) → 1, one obtains ρ(δ) → 0 and

```text
ρ′(δ) = Re(conj(s(δ)) s′(δ)) / |s(δ)| → 1.
```

Let δ decrease to zero. This gives ρ(h) ≥ sin(Kh)/K. Letting h increase to h₀ contradicts the alleged zero. The endpoint h = π/K has zero right-hand side and needs no nonvanishing claim. Every regularity and variation-of-constants step remains to be formalized.

## Capped Fourier moment without an optimizer selection

Let μ be the cell mass and λ = Kμ/Q. The interval-length and density constraints give 0 ≤ λ ≤ π. Extend q by zero to a full period and choose a phase aligning its nonzero complex Fourier moment; handle the zero-moment case separately.

For c = cos λ, the pointwise inequality

```text
q cos θ ≤ c q + Q max(cos θ − c, 0)
```

holds whenever 0 ≤ q ≤ Q. Over one full period in the physical coordinate,

```text
∫ max(cos(2Kz − φ) − cos λ, 0) dz
  = (sin λ − λ cos λ)/K.
```

Integrating the pointwise inequality therefore gives

```text
|∫ q(z) exp(2iKz) dz|
  ≤ μ cos λ + (Q/K)(sin λ − λ cos λ)
  = (Q/K) sin λ.
```

This proves the same capped moment bound using periodic integration and elementary calculus, without selecting a wrapped maximizing arc. Measurability, integrability, and the positive-part integral remain explicit Lean obligations.

## Remaining lower bound dependencies

The Gram identity must be proved for the actual Maxwell fields, including the factor T and the Wronskian normalization. It cannot be introduced as an assumption about arbitrary matrices. The required identity is

```text
det(A_J)/T = 4k⁴ ∫_{x<y in J} q(x)q(y)|s(y,x)|² dx dy.
```

For the aggregation step, prove the determinant Minkowski inequality for Hermitian positive semidefinite 2 by 2 matrices. Use half-open partition cells or explicitly remove duplicated endpoints of measure zero.

For f(u) = u² − sin²u and g(u) = √f(u), the paper establishes convexity only on [0, π/2]. The tangent at 0 < x ≤ 1/3 supports g on all of [0, π]; this is a separate theorem. Extending the convexity claim to [0, π] would be false. Theorem 4.5 uses the former result for half-period cells and the latter result when the full-period mean is small.

The uniform asymptotic floor requires quantification over varying admissible profiles and thickness budgets, with fixed k, P, Q, M. A theorem for one fixed profile is insufficient. The target coefficient is π²(kM)⁴/(3PQ²).

## Cell asymptotics without matrix logarithms

Use a submultiplicative matrix operator norm with norm(I) = 1. Let

```text
A = i [[0, 1], [P, 0]]
B = −Q E₂₁
D(ξ) = exp(−Aξ/2) exp((A+B)ξ) exp(−Aξ/2)
C₃ = [[0, −Q], [Q(P+2iQ), 0]] / 12.
```

The fixed-matrix exponential Taylor remainder satisfies

```text
norm(exp(ξX) − Σ_{j=0}^4 ξʲ Xʲ/j!)
  ≤ |ξ|⁵ norm(X)⁵ exp(|ξ| norm(X))/5!.
```

Multiplication gives the linear coefficient B, the zero quadratic coefficient, and the stated C₃. The exact identity D(−ξ)D(ξ) = I then determines the fourth coefficient, giving

```text
D(ξ) = I + ξB + ξ³C₃ + (ξ⁴/2)(BC₃+C₃B) + O(|ξ|⁵).
```

Put g₀ = kM, G = −g₀E₂₁, H = g₀³C₃/Q³, and K₄ = (GH+HG)/2. For positive integers m,

```text
D_m = D(g₀/(Qm)) = A_m + W_m
A_m = I + G/m
W_m = H/m³ + K₄/m⁴ + R_m
norm(R_m) ≤ C_R/m⁵
G² = 0.
```

Thus A_mʲ = I + (j/m)G. Choose C so that norm(A_m) and norm(D_m) are at most 1+C/m for sufficiently large m. Double telescoping bounds the difference between D_mᵐ and its first-insertion expansion by

```text
norm(D_mᵐ − A_mᵐ − Σ_{j=0}^{m−1} A_mʲ W_m A_m^(m−1−j))
  ≤ [m(m−1)/2] norm(W_m)² (1+C/m)^(m−2)
  = O(m⁻⁴).
```

Inserting R_m in the finite sum contributes O(m⁻⁴). The H and K₄ terms sum exactly to

```text
J/m² − GHG/(6m⁴),
J = H + (GH+HG)/2 + GHG/6.
```

Therefore the exact stripped physical core satisfies

```text
F_m = D_mᵐ = I + G + J/m² + O(m⁻⁴).
```

This recovers the manuscript’s full remainder without a matrix logarithm or a derivative formula for the exponential at a noncommuting matrix. Since J₁₂ = −g₀³/(12Q²), the defect determinant is

```text
c_m = det(Σ − F_m† Σ F_m)
    = g₀⁴/(3Q²m²) + O(m⁻⁴),
Σ = [[0, 1], [1, 0]].
```

The finite identities and estimates above were independently checked mathematically. Their Lean proofs remain unwritten and uncompiled.

## Exact matching with matrix entries as parameters

A parameter implicit-function theorem can use all eight real entries of the core matrix. No analytic interpolation of the integer m is needed.

For an arbitrary complex matrix F, set H_w = [[1,1],[1,−1]], K(F) = H_w⁻¹ F H_w, and d = K(F)₂₂. On the open set d ≠ 0 define

```text
r_L = −K(F)₂₁/d
r_R = K(F)₁₂/d
t_R = 1/d
t_L = det(F)/d
T_ext(F) = |t_L|²
a_ext(F) = 1 − (|r_L|² + |r_R|² + |t_L|² + |t_R|²)/2.
```

These are smooth real rational functions. On the actual unimodular physical matrices they agree with the paper’s T and a. The extension permits an ordinary implicit-function theorem on an open subset of real dimension ten, while the constructed sequence retains determinant one.

Let Λ(ℓ) = diag(exp ℓ, exp(−ℓ)) and use the two coating parameters in Λ(ℓ_R) F Λ(ℓ_L). At the limiting sheet F₀ = I+G, put A_s = exp(ℓ_L+ℓ_R), h = g₀ exp(ℓ_L−ℓ_R), and v = A_s + 1/A_s. The response is

```text
T = 4/(v+h)²
a = 2hv/(v+h)².
```

The derivative determinant in the two coating unknowns is

```text
[−16(v−h)/(v+h)⁵] (1−A_s⁻²) (−2A_s h).
```

At the target, A_s = A₀ lies in (0,1), h = h₀ > 0, and v−h = 2s/√T > 0. Hence the derivative is invertible. The implicit theorem gives a differentiable matching map F ↦ (ℓ_L(F), ℓ_R(F)); differentiability gives a bound by a constant times norm(F−F₀). Evaluation at F_m proves coating changes of order m⁻² and exact target equality for all sufficiently large integers m.

The derivative, open domain, matching equation, and estimate all remain to be proved in Lean. The final theorem must retain exact target equality.

## Physical coatings and the phase estimate

For each matching side choose a fixed positive integer j with |ℓ₀|/j < (log P)/2. For nearby ℓ define

```text
n₁ = P^(1/4) exp(ℓ/(2j))
n₂ = P^(1/4) exp(−ℓ/(2j)).
```

Both indices remain strictly between 1 and √P. Repeating j quarter-wave pairs implements diag(exp ℓ, exp(−ℓ)) up to a scalar sign. Each pair has thickness less than π/k, so the two coating networks have a uniform thickness bound. Including the two end quarter waves of the core,

```text
kL_m ≤ πm/√P + C_phys
C_phys = π/√P + π(j_L+j_R).
```

The m lossy slices have width M/(Qm), so their integrated imaginary permittivity is exactly M. All remaining layers are lossless. Scalar signs leave reflections unchanged and only reverse the transmission amplitude, preserving all target powers.

Section 5.4’s statement θ = π + O(m⁻²) requires a locally continuous phase branch. As a statement about principal arguments it is not justified at the branch cut. The needed bound can be proved without any argument function. For the nonzero matched scattering entries define

```text
ζ = r_L r_R conj(t)² / (T |r_L r_R|).
```

Then |ζ| = 1 and ζ+1 = O(m⁻²). The exact phase penalty is

```text
2T |r_L r_R| (1 + Re ζ)
  = T |r_L r_R| |ζ+1|²
  = O(m⁻⁴).
```

This repairs the phase ambiguity without changing Theorem 5.1. Together with the scalar envelope it gives D₀−D_m = αc_m + O(m⁻⁴).

## Supremum and all thickness budgets

For sufficiently large real L choose

```text
m(L) = floor(√P (kL − C_phys)/π).
```

This is eventually a sufficiently large positive integer, the corresponding physical stack fits the budget, and m(L)/(kL) → √P/π. Thus the class is eventually nonempty.

The image of this class under D is bounded above by D₀. If β(L) is the uniform resource floor from Theorem 4.5, the final squeeze is

```text
α β(L) ≤ D₀ − D*(L) ≤ D₀ − D_{m(L)}.
```

The scaled lower and upper limits coincide. This argument does not require attainment of the supremum. Nonemptiness, boundedness, the uniform lower bound, the floor estimates, and each use of the real supremum remain explicit formal obligations.

## Mathlib dependencies and proof integrity

The [official algebra logarithm module](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/Logarithm.html) inspected in this audit lists exponential inverse identities and analyticity as unfinished developments. Its definition alone does not justify the logarithm manipulations in the manuscript. The direct repeated-product argument above avoids that dependency. This is a documentation observation, not a claim about a successfully compiled pinned checkout.

Mathlib provides [implicit-function infrastructure](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Implicit.html). Its hypotheses must be discharged for the explicit real rational response map; the nonzero Jacobian calculation alone is insufficient.

The reproducible project must pin the Lean toolchain and Mathlib commit, retain its dependency manifest, import every claimed theorem through the default Lake target, and preserve a successful clean build log. Every completed public theorem, including Theorem 5.1, must have a printed dependency-axiom report. Reject `sorryAx`, added mathematical axioms, and native-evaluation axioms. Any use of Lean’s standard logical foundations `propext`, `Classical.choice`, and `Quot.sound` should be reported transparently, following the [official proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

No completed Lean source, successful build, axiom report, or reproducible proof project is claimed by this checkpoint.
