# Physical static Newton operator — verified; Theorem 1.1 PARTIAL

This continuation preserves every Lean module from `8301dda82eaf84611a4a40982f77dc2787b16861`. The original physical target and manuscript are unchanged. The physical static operator identification is proved on the entire original compactly supported vector L² current class, directly, including nonsmooth currents. No smooth-class surrogate or assumed physical identity is used.

The principal declarations in `PrescribedExtinction/NewtonStaticIdentification.lean` are:

```lean
theorem outgoingVolumeDistribution_zero_eq_staticFourier
    (p : CompactPolarization) (i : Fin 3) :
    outgoingVolumeDistribution 0 p i =
      vectorL2ComponentDistribution
        (staticFourierOperator (p.memLp.toLp p.current)) i

theorem outgoingVolumeDistribution_zero_bounded_L2_realization
    (p : CompactPolarization) :
    ∃ u : VectorL2,
      (∀ i : Fin 3, outgoingVolumeDistribution 0 p i =
        vectorL2ComponentDistribution u i) ∧
      ‖u‖ ≤ ‖p.memLp.toLp p.current‖
```

Both sides are in the original continuous distribution framework on the original real `ScalarTest`. `outgoingVolumeDistribution` is the unchanged actual convolution followed by distributional Hessian derivatives, so the verified Newton contact term is retained. The L² realization is the existing Fourier multiplier, now justified as physical by the first theorem.

The proof dependencies are genuine analytical bridges:

- `NewtonCurrentPairing`: compact L² currents are L¹; both actual double integrands are absolutely integrable by a finite kernel cutoff; Fubini identifies the physical potential with the actual current/test correlation.
- `NewtonCurrentCorrelation`: that correlation is compact, smooth and Schwartz, and its derivatives commute with the original test derivatives. Mathlib's differentiated convolution theorem supplies these identities.
- `FourierL1L2`: the actual Fourier integral agrees almost everywhere with Mathlib's L² transform for every L¹∩L² complex Hilbert-valued function, including the actual vector current. This follows from true Fourier pairing and distribution uniqueness.
- `NewtonCurrentFourier`: the actual reflected-current correlation has the exact inverse-Fourier product formula. Both convolution factors are genuinely L¹; the Newton kernel itself is not treated as globally L¹.
- `StaticOperatorDistribution`: the existing bounded Fourier operator induces an actual distribution on the original tests, with its exact component integral formula.
- `NewtonStaticIdentification`: combines those bridges with the previously verified full Newton Hessian Fourier identity. The proof covers all `CompactPolarization` inputs directly, so no density extension remains unproved for this class.

The principal declarations and all supporting public/private project constants are transitively audited using `#print axioms` and Lean's identical `collectAxioms` collector for private canonical names. The only permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom axioms or native proof shortcuts are permitted.

Reproduction uses the pinned toolchain and dependencies described in README:

```powershell
./configure.ps1
./verify.ps1 -Clean
./verify-milestones.ps1
```

`verification/clean-build.log`, `verification/axioms.log`, `verification/statements.log`, and the six new directories in `verification/milestones/` contain the reproducible evidence. The earlier Fourier evidence is preserved under `verification/milestones/pre-static/`.

Next is the actual outgoing dyadic operator: prove that the dynamic-minus-static distribution has exactly the existing locally integrable classical remainder and no additional contact term, then connect its actual convolution and bounded compact-domain realization. The positive-frequency fundamental solution, Maxwell representation, scattering existence/uniqueness, radiation identity, optical theorem, reciprocity, uniform aperture localization and the prescribed-extinction construction remain unverified. `Theorem11Statement` is still an unproved definition; there is no final physical theorem proof declaration.
