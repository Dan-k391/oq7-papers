import PrescribedExtinction.PlanarReflectedLayer

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Classical

def planarLayerL2Current (k a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (F : PlanarLayerField k a b) : PlanarCurrentL2 L :=
  ⟨(continuousOn_Ioc_indicator_memLp a b F.current F.current_continuous).toLp
    ((Ioc a b).indicator F.current), by
    filter_upwards [(continuousOn_Ioc_indicator_memLp a b F.current F.current_continuous).coeFn_toLp] with z hz
    intro hn
    rw [hz]
    exact indicator_of_notMem (fun hm => hn ⟨ha.trans hm.1.le, hm.2.trans hb⟩) _⟩

theorem planarLayerL2Current_coe (k a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (F : PlanarLayerField k a b) :
    (planarLayerL2Current k a b L ha hab hb F : HeightL2) =ᵐ[volume] (Ioc a b).indicator F.current :=
  (continuousOn_Ioc_indicator_memLp a b F.current F.current_continuous).coeFn_toLp

theorem scalarPlanarPotential_layer_current (k a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (F : PlanarLayerField k a b) (z : ℝ) :
    scalarPlanarPotential k (planarLayerL2Current k a b L ha hab hb F : HeightL2) z =
      ∫ t in a..b, planarScalarGreen k (z - t) * F.current t := by
  change (∫ t : ℝ, planarScalarGreen k (z - t) * (planarLayerL2Current k a b L ha hab hb F : HeightL2) t) = _
  calc
    _ = ∫ t : ℝ, planarScalarGreen k (z - t) * (Ioc a b).indicator F.current t := by
      apply integral_congr_ae
      filter_upwards [planarLayerL2Current_coe k a b L ha hab hb F] with t ht
      rw [ht]
    _ = _ := planarGreen_integral_indicator k a b z hab F.current

theorem scalarPlanarPotential_layer_interior (k a b L : ℝ) (hk : k ≠ 0)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) (F : PlanarLayerField k a b)
    (z : ℝ) (hz : z ∈ Icc a b) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k (planarLayerL2Current k a b L ha hab hb F : HeightL2) z =
      F.electric z - (1 / 2 : ℂ) * apertureOscillation k (z - a) * (F.magnetic a + F.electric a) +
        (1 / 2 : ℂ) * apertureOscillation k (b - z) * (F.magnetic b - F.electric b) := by
  rw [scalarPlanarPotential_layer_current, Complex.real_smul, Complex.ofReal_pow]
  exact planarGreen_interval_interior_representation k a b z hk hz.1 hz.2 F.electric F.magnetic F.current
    F.electric_continuous F.magnetic_continuous F.current_continuous F.electric_derivative F.magnetic_derivative

theorem scalarPlanarPotential_layer_exterior_left (k a b L : ℝ) (hk : k ≠ 0)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) (F : PlanarLayerField k a b)
    (z : ℝ) (hz : z ≤ a) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k (planarLayerL2Current k a b L ha hab hb F : HeightL2) z =
      (1 / 2 : ℂ) * apertureOscillation k (b - z) * (F.magnetic b - F.electric b) -
        (1 / 2 : ℂ) * apertureOscillation k (a - z) * (F.magnetic a - F.electric a) := by
  rw [scalarPlanarPotential_layer_current, Complex.real_smul, Complex.ofReal_pow]
  exact planarGreen_interval_exterior_left_representation k a b z hk hab hz F.electric F.magnetic F.current
    F.electric_continuous F.magnetic_continuous F.current_continuous F.electric_derivative F.magnetic_derivative

theorem scalarPlanarPotential_layer_exterior_right (k a b L : ℝ) (hk : k ≠ 0)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) (F : PlanarLayerField k a b)
    (z : ℝ) (hz : b ≤ z) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k (planarLayerL2Current k a b L ha hab hb F : HeightL2) z =
      (1 / 2 : ℂ) * apertureOscillation k (z - b) * (F.magnetic b + F.electric b) -
        (1 / 2 : ℂ) * apertureOscillation k (z - a) * (F.magnetic a + F.electric a) := by
  rw [scalarPlanarPotential_layer_current, Complex.real_smul, Complex.ofReal_pow]
  exact planarGreen_interval_exterior_right_representation k a b z hk hab hz F.electric F.magnetic F.current
    F.electric_continuous F.magnetic_continuous F.current_continuous F.electric_derivative F.magnetic_derivative

end OQ7Prescribed
