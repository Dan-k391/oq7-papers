import GeneralizedResearch.BeamPackets

/-! Literal transverse-momentum reversal for the actual oblique material
family and its even, finite-power disk packets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.BeamTimeReversal
open MeasureTheory ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis ObliqueFamily
open BeamFibers BeamPackets FiniteHilbertBridge
open scoped Matrix

theorem square_neg (κ : ObliqueVacuum.Transverse) : square (-κ) = square κ := by
  simp [square]

theorem radial_neg (κ : ObliqueVacuum.Transverse) : radial (-κ) = radial κ := by
  ext i j
  simp [radial, Matrix.vecMulVec_apply]

theorem perpendicular_neg (κ : ObliqueVacuum.Transverse) : perpendicular (-κ) = -perpendicular κ := by
  ext i
  fin_cases i <;> simp [perpendicular]

theorem longitudinal_neg (k : ℝ) (κ : ObliqueVacuum.Transverse) :
    longitudinal k (-κ) = longitudinal k κ := by simp only [longitudinal, square_neg]

theorem rootAdmittance_neg (k : ℝ) (κ : ObliqueVacuum.Transverse) :
    rootAdmittance k (-κ) = rootAdmittance k κ := by
  simp only [rootAdmittance, root, coefficient, longitudinal_neg, radial_neg]

theorem invRootAdmittance_neg (k : ℝ) (κ : ObliqueVacuum.Transverse) :
    invRootAdmittance k (-κ) = invRootAdmittance k κ := by
  simp only [invRootAdmittance, root, coefficient, longitudinal_neg, radial_neg]

theorem generator_neg (k : ℝ) (κ : ObliqueVacuum.Transverse) (R Q : RMat) :
    generator k (-κ) R Q = generator k κ R Q := by
  simp only [generator, electricBlock, materialBlock, realBlock, perpendicular_neg, radial_neg]

theorem transfer_neg (k : ℝ) (κ : ObliqueVacuum.Transverse) (R Q : RMat) (d : ℝ) :
    transfer k (-κ) R Q d = transfer k κ R Q d := by
  simp only [transfer, generator_neg]

theorem basis_neg (k : ℝ) (κ : ObliqueVacuum.Transverse) : basis k (-κ) = basis k κ := by
  simp only [basis, U, V, rootAdmittance_neg, invRootAdmittance_neg]

theorem inverse_neg (k : ℝ) (κ : ObliqueVacuum.Transverse) : inverse k (-κ) = inverse k κ := by
  simp only [inverse, U, V, rootAdmittance_neg, invRootAdmittance_neg]

theorem fieldTransfer_neg (k η h : ℝ) (j : ℕ) (κ : ObliqueVacuum.Transverse) (t : ℝ) :
    fieldTransfer k η h j (-κ) t = fieldTransfer k η h j κ t := by
  simp only [fieldTransfer, transfer_neg]

theorem waveTransfer_neg (k η h : ℝ) (j : ℕ) (κ : ObliqueVacuum.Transverse) (t : ℝ) :
    ObliqueFamily.waveTransfer k η h j (-κ) t = ObliqueFamily.waveTransfer k η h j κ t := by
  simp only [ObliqueFamily.waveTransfer, ObliqueWaveBasis.waveTransfer,
    fieldTransfer_neg, basis_neg, inverse_neg]

theorem response_neg (k η h : ℝ) (j : ℕ) (κ : ObliqueVacuum.Transverse) (t : ℝ) :
    response k η h j (-κ) t = response k η h j κ t := by
  simp only [response, waveTransfer_neg]

theorem reference_neg (k d : ℝ) (κ : ObliqueVacuum.Transverse) :
    reference k d (-κ) = reference k d κ := by
  simp only [reference, phase, longitudinal_neg]

theorem ofLp_neg (q : BeamAveraging.Transverse) : WithLp.ofLp (-q) = -WithLp.ofLp q := rfl

theorem aperture_neg (r : ℝ) (q : BeamAveraging.Transverse) :
    BeamAveraging.aperture volume (disk r) (-q) = BeamAveraging.aperture volume (disk r) q := by
  have he : (-q) ∈ disk r ↔ q ∈ disk r := by
    simp only [disk, Metric.mem_closedBall, dist_zero_right, norm_neg]
  by_cases hq : q ∈ disk r
  · have hn := he.mpr hq
    simp [BeamAveraging.aperture, Set.indicator, hq, hn]
  · have hn : -q ∉ disk r := fun h => hq (he.mp h)
    simp [BeamAveraging.aperture, Set.indicator, hq, hn]

abbrev Fiber := EuclideanSpace ℂ Channel

/-- Time reversal conjugates the vacuum-reference output and reverses q. -/
def reversedSpectrum (S0 : BeamAveraging.Transverse → Mat4)
    (f : BeamAveraging.Transverse → Fiber) (q : BeamAveraging.Transverse) : Fiber :=
  vector (star (S0 (-q) *ᵥ WithLp.ofLp (f (-q))))

theorem reversed_packet (r : ℝ) (S0 : BeamAveraging.Transverse → Mat4)
    (hS0 : ∀ q, S0 (-q) = S0 q) (u : Channel → ℂ) :
    reversedSpectrum S0 (packet r (fun _ => vector u)) =
      packet r (fun q => vector (ChannelPowers.reverse (S0 q) u)) := by
  funext q
  change vector (star (S0 (-q) *ᵥ ((BeamAveraging.aperture volume (disk r) (-q) : ℂ) • u))) =
    (BeamAveraging.aperture volume (disk r) q : ℂ) • vector (ChannelPowers.reverse (S0 q) u)
  rw [hS0 q, aperture_neg, Matrix.mulVec_smul, star_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rfl

theorem actual_reversed_packet (k d r : ℝ) :
    reversedSpectrum (fun q => reference k d (WithLp.ofLp q))
      (packet r (fun _ => vector left)) =
        packet r (fun q => vector (ChannelPowers.reverse (reference k d (WithLp.ofLp q)) left)) := by
  apply reversed_packet
  intro q
  rw [ofLp_neg, reference_neg]

theorem response_ofLp_neg (k η h : ℝ) (j : ℕ) (q : BeamAveraging.Transverse) (t : ℝ) :
    response k η h j (WithLp.ofLp (-q)) t = response k η h j (WithLp.ofLp q) t := by
  rw [ofLp_neg, response_neg]

end GeneralizedResearch.BeamTimeReversal
