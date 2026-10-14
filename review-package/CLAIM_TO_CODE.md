# S1 — Theorem correspondence and scope

Frozen source commit: 686402a6c2d63820828729cc7ab02504632e3fe7.
Declaration: OQ7Prescribed.theorem11_complete : OQ7Prescribed.PhysicalTheorem11Statement.

The accompanying CSV/HTML identifies individual source declarations, actual source locations, consequences, and exposition that is not separately formalized. The new reproduction also checks that every OQ7Prescribed declaration named by the CSV exists in the aggregate environment; this existence check does not replace the completed semantic audit.

| Manuscript claim | Evidence / code relationship |
|---|---|
| Fixed k>0; arbitrary fixed P>1,Q>0; every E*>0 and every 0<epsilon<1 | Theorem11Statement existence core; first conjunct of PhysicalTheorem11Statement |
| Same unchanged object for the two sources | One TwoLayerBody supplies both plus/minus ScatteringState values; different tensors across the two layers are permitted |
| Opposite real y-polarized unit-amplitude plane waves | incidentElectric / Direction definitions and Maxwell model; source reversal changes propagation, not material |
| Local, reciprocal, anisotropic, nonmagnetic two-layer dielectric body | TwoLayerBody, MaterialAdmissible, weak Maxwell definitions; vacuum exterior; constant tensors in each layer |
| I<=Re_H epsilon<=PI and 0<Im_H epsilon<=QI | Hermitian quadratic-form bounds in MaterialAdmissible |
| Exactly X+=X-=E* | Theorem11Statement and PrescribedExtinctionPair; not numerical target tolerance or rescaled incident intensity |
| Gamma=abs(A+−A−)/X=abs(S+−S−)/X | Energy balance, arbitrary-state reciprocal extinction, and universal_physical_asymmetry_eq_scattering_difference |
| Complete outgoing radiation | FullPhysicalOpticalStatement: continuous current far field, uniform radiation asymptotics and limiting full-sphere Poynting flux; both transverse polarizations included |
| Sup Gamma=1; sup dimensional absorption difference=E* | Full-class value sets and both sSup conjuncts of PhysicalTheorem11Statement |
| Strict nonattainment | Universal strict bound at positive extinction and final PrescribedExtinctionPair inequalities; auditor_extinction_pos additionally removes the zero-extinction branch for admissible bodies |
| Unrestricted dimensions and no common positive loss floor across the sequence | The admissible class contains arbitrary finite positive R,h,d; only upper material caps and per-body strict loss are imposed. No common resource ceiling or positive loss floor is asserted |
| Main theorem, not every displayed intermediate argument | October 11 Theorem 1.1/Lemma 1.2 correspond to review Theorem 4.1/Lemma 4.2. The Weyl/Fourier proof presentation and displayed planar vectors are not all individually exported Lean statements |

The physical strictness proof in Lean and the manuscript's continuous-far-field argument have different organizations and the same main conclusion. Ordinary exposition, floating-point diagnostics and drawings are not described as independently kernel-checked statements.

Supplemental auditor theorems remain unchanged in release/evidence/final/experiments/Audit2.lean and the S4 evidence. They are accompanying checks, not silent alterations of the frozen main theorem.

