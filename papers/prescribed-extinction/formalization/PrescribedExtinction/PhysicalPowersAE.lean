import PrescribedExtinction.PhysicalPolarization

noncomputable section
namespace OQ7Prescribed
open MeasureTheory

theorem polarization_congr_ae (B : TwoLayerBody) (E F : Field) (h : E =ᵐ[volume] F) :
    polarization B E =ᵐ[volume] polarization B F := by
  filter_upwards [h] with x hx
  simp only [polarization, hx]

theorem extinction_congr_ae (k : ℝ) (B : TwoLayerBody) (σ : Direction) (E F : Field)
    (h : E =ᵐ[volume] F) : extinction k B σ E = extinction k B σ F := by
  unfold extinction
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (polarization_congr_ae B E F h)] with x hx
  rw [hx]

theorem absorption_congr_ae (k : ℝ) (B : TwoLayerBody) (E F : Field)
    (h : E =ᵐ[volume] F) : absorption k B E = absorption k B F := by
  unfold absorption
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae h] with x hx
  rw [hx]

theorem currentFarField_congr_ae (k : ℝ) (B : TwoLayerBody) (E F : Field)
    (h : E =ᵐ[volume] F) : currentFarField k B E = currentFarField k B F := by
  funext n
  unfold currentFarField
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (polarization_congr_ae B E F h)] with x hx
  rw [hx]

theorem scattering_congr_ae (k : ℝ) (B : TwoLayerBody) (E F : Field)
    (h : E =ᵐ[volume] F) : scattering k B E = scattering k B F := by
  unfold scattering
  rw [currentFarField_congr_ae k B E F h]

end OQ7Prescribed
