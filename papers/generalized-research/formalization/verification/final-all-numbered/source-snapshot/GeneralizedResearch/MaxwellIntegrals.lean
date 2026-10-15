import GeneralizedResearch.SuperposedMaxwell
import GeneralizedResearch.PhysicalFourierIntegral

/-! Literal classical curls of compact physical-angular-frequency superpositions. -/
noncomputable section
namespace GeneralizedResearch.MaxwellIntegrals
open MeasureTheory Set SuperposedMaxwell BeamPackets BeamSuperposition FourierMaxwell
open scoped Matrix Topology
abbrev Transverse := BeamAveraging.Transverse
abbrev Spatial := SuperposedMaxwell.Spatial

def superposedElectric (r k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→ObliqueMaxwell.Channel→ℂ)
    (p:Spatial) : Vec3 := fun i=> (PhysicalFourier.factor:ℂ)*∫q in disk r,electricPlane k R Q u (p,q) i

def superposedMagnetic (r k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→ObliqueMaxwell.Channel→ℂ)
    (p:Spatial) : Vec3 := fun i=> (PhysicalFourier.factor:ℂ)*∫q in disk r,magneticPlane k R Q u (p,q) i

theorem coordinate_line (j:Fin 3) (p:Spatial) : line j p (coordinate p j)=p := by
  fin_cases j <;> rfl

theorem component_continuousOn {Y:Type*} [TopologicalSpace Y] {B:Set Y} {F:Y→Vec3}
    (hF:ContinuousOn F B) (i:Fin 3) : ContinuousOn (fun p=>F p i) B :=
  fun p hp=>continuousWithinAt_pi.mp (hF p hp) i

theorem plane_integrable (r k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→ObliqueMaxwell.Channel→ℂ)
    (hu:ContinuousOn u (disk r)) (p:Spatial) (i:Fin 3) :
    IntegrableOn (fun q=>electricPlane k R Q u (p,q) i) (disk r) ∧
      IntegrableOn (fun q=>magneticPlane k R Q u (p,q) i) (disk r) := by
  have hc := plane_continuousOn k r R Q u hu
  have hmap : Continuous (fun q:Transverse=>(p,q)) := continuous_const.prodMk continuous_id
  exact ⟨((component_continuousOn hc.1 i).comp hmap.continuousOn (fun q hq=>⟨mem_univ _,hq⟩)).integrableOn_compact (isCompact_closedBall _ _),
    ((component_continuousOn hc.2 i).comp hmap.continuousOn (fun q hq=>⟨mem_univ _,hq⟩)).integrableOn_compact (isCompact_closedBall _ _)⟩

theorem partial_integrable (r k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→ObliqueMaxwell.Channel→ℂ)
    (hu:ContinuousOn u (disk r)) (p:Spatial) (j i:Fin 3) :
    IntegrableOn (fun q=>electricPartial k R Q u j (p,q) i) (disk r) ∧
      IntegrableOn (fun q=>magneticPartial k R Q u j (p,q) i) (disk r) := by
  have hc := partial_continuousOn k r R Q u hu j
  have hmap : Continuous (fun q:Transverse=>(p,q)) := continuous_const.prodMk continuous_id
  exact ⟨((component_continuousOn hc.1 i).comp hmap.continuousOn (fun q hq=>⟨mem_univ _,hq⟩)).integrableOn_compact (isCompact_closedBall _ _),
    ((component_continuousOn hc.2 i).comp hmap.continuousOn (fun q hq=>⟨mem_univ _,hq⟩)).integrableOn_compact (isCompact_closedBall _ _)⟩

theorem superposed_partial (r k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→ObliqueMaxwell.Channel→ℂ)
    (hu:ContinuousOn u (disk r)) (p:Spatial) (j i:Fin 3) :
    HasDerivAt (fun x=>superposedElectric r k R Q u (line j p x) i)
      ((PhysicalFourier.factor:ℂ)*∫q in disk r,electricPartial k R Q u j (p,q) i) (coordinate p j) ∧
      HasDerivAt (fun x=>superposedMagnetic r k R Q u (line j p x) i)
        ((PhysicalFourier.factor:ℂ)*∫q in disk r,magneticPartial k R Q u j (p,q) i) (coordinate p j) := by
  let x0 := coordinate p j
  have hmap : Continuous (fun w:ℝ×Transverse=>(line j p w.1,w.2)) :=
    ((line_continuous j p).comp continuous_fst).prodMk continuous_snd
  have hsub : MapsTo (fun w:ℝ×Transverse=>(line j p w.1,w.2))
      (Icc (x0-1) (x0+1) ×ˢ disk r) (univ ×ˢ disk r) := fun w hw=>⟨mem_univ _,hw.2⟩
  have hc := plane_continuousOn k r R Q u hu
  have hc' := partial_continuousOn k r R Q u hu j
  have he := compact_parameter_derivative r x0
    (fun x q=>electricPlane k R Q u (line j p x,q) i)
    (fun x q=>electricPartial k R Q u j (line j p x,q) i)
    ((component_continuousOn hc.1 i).comp hmap.continuousOn hsub)
    ((component_continuousOn hc'.1 i).comp hmap.continuousOn hsub)
    (fun q _ x _=>(plane_partial k R Q u q p j i x).1)
  have hm := compact_parameter_derivative r x0
    (fun x q=>magneticPlane k R Q u (line j p x,q) i)
    (fun x q=>magneticPartial k R Q u j (line j p x,q) i)
    ((component_continuousOn hc.2 i).comp hmap.continuousOn hsub)
    ((component_continuousOn hc'.2 i).comp hmap.continuousOn hsub)
    (fun q _ x _=>(plane_partial k R Q u q p j i x).2)
  constructor
  · simpa only [superposedElectric,x0,coordinate_line] using he.const_mul (PhysicalFourier.factor:ℂ)
  · simpa only [superposedMagnetic,x0,coordinate_line] using hm.const_mul (PhysicalFourier.factor:ℂ)

def partialCurl (F:Fin 3→Vec3) : Vec3 := ![F 1 2-F 2 1,F 2 0-F 0 2,F 0 1-F 1 0]

theorem pointwise_maxwell (k:ℝ) (hk:k≠0) (R Q:ObliqueVacuum.RMat)
    (u:Transverse→ObliqueMaxwell.Channel→ℂ) (p:Spatial) (q:Transverse) :
    partialCurl (fun j=>electricPartial k R Q u j (p,q))=(Complex.I*(k:ℂ)) • magneticPlane k R Q u (p,q) ∧
      partialCurl (fun j=>magneticPartial k R Q u j (p,q))=
        (-(Complex.I*(k:ℂ))) • constitutive R Q (electricPlane k R Q u (p,q)) := by
  have hm := fourier_maxwell k hk (WithLp.ofLp q) R Q (fiberState k R Q u (p,q))
  have he : partialCurl (fun j=>electricPartial k R Q u j (p,q))=
      phase (WithLp.ofLp q) p.1 p.2.1 • fourierCurl (WithLp.ofLp q)
        (electric k (WithLp.ofLp q) (fiberState k R Q u (p,q)))
        (electric k (WithLp.ofLp q) (derivativeState k R Q u (p,q))) := by
    ext i;fin_cases i <;> simp [partialCurl,electricPartial,electricPlane,fourierCurl] <;> ring
  have hh : partialCurl (fun j=>magneticPartial k R Q u j (p,q))=
      phase (WithLp.ofLp q) p.1 p.2.1 • fourierCurl (WithLp.ofLp q)
        (magnetic k (WithLp.ofLp q) (fiberState k R Q u (p,q)))
        (magnetic k (WithLp.ofLp q) (derivativeState k R Q u (p,q))) := by
    ext i;fin_cases i <;> simp [partialCurl,magneticPartial,magneticPlane,fourierCurl] <;> ring
  rw [he,hh]
  unfold derivativeState
  rw [hm.1,hm.2]
  constructor
  · simp [magneticPlane,smul_smul,mul_comm]
  · simp [electricPlane,constitutive_smul,smul_smul,mul_comm]


theorem curl_integral_electric (r k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→ObliqueMaxwell.Channel→ℂ)
    (hu:ContinuousOn u (disk r)) (x y z:ℝ) :
    curl (fun x y z=>superposedElectric r k R Q u (x,y,z)) x y z=
      fun i=>(PhysicalFourier.factor:ℂ)*∫q in disk r,partialCurl (fun j=>electricPartial k R Q u j ((x,y,z),q)) i := by
  have hx (i:Fin 3) : deriv (fun a=>superposedElectric r k R Q u (a,y,z) i) x=
      (PhysicalFourier.factor:ℂ)*∫q in disk r,electricPartial k R Q u 0 ((x,y,z),q) i :=
    (superposed_partial r k R Q u hu (x,y,z) 0 i).1.deriv
  have hy (i:Fin 3) : deriv (fun a=>superposedElectric r k R Q u (x,a,z) i) y=
      (PhysicalFourier.factor:ℂ)*∫q in disk r,electricPartial k R Q u 1 ((x,y,z),q) i :=
    (superposed_partial r k R Q u hu (x,y,z) 1 i).1.deriv
  have hz (i:Fin 3) : deriv (fun a=>superposedElectric r k R Q u (x,y,a) i) z=
      (PhysicalFourier.factor:ℂ)*∫q in disk r,electricPartial k R Q u 2 ((x,y,z),q) i :=
    (superposed_partial r k R Q u hu (x,y,z) 2 i).1.deriv
  have hi (j i:Fin 3) := (partial_integrable r k R Q u hu (x,y,z) j i).1
  ext i;fin_cases i
  · simp [curl,partialCurl,hx,hy,hz]
    rw [integral_sub (hi 1 2) (hi 2 1)];ring
  · simp [curl,partialCurl,hx,hy,hz]
    rw [integral_sub (hi 2 0) (hi 0 2)];ring
  · simp [curl,partialCurl,hx,hy,hz]
    rw [integral_sub (hi 0 1) (hi 1 0)];ring

theorem curl_integral_magnetic (r k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→ObliqueMaxwell.Channel→ℂ)
    (hu:ContinuousOn u (disk r)) (x y z:ℝ) :
    curl (fun x y z=>superposedMagnetic r k R Q u (x,y,z)) x y z=
      fun i=>(PhysicalFourier.factor:ℂ)*∫q in disk r,partialCurl (fun j=>magneticPartial k R Q u j ((x,y,z),q)) i := by
  have hx (i:Fin 3) : deriv (fun a=>superposedMagnetic r k R Q u (a,y,z) i) x=
      (PhysicalFourier.factor:ℂ)*∫q in disk r,magneticPartial k R Q u 0 ((x,y,z),q) i :=
    (superposed_partial r k R Q u hu (x,y,z) 0 i).2.deriv
  have hy (i:Fin 3) : deriv (fun a=>superposedMagnetic r k R Q u (x,a,z) i) y=
      (PhysicalFourier.factor:ℂ)*∫q in disk r,magneticPartial k R Q u 1 ((x,y,z),q) i :=
    (superposed_partial r k R Q u hu (x,y,z) 1 i).2.deriv
  have hz (i:Fin 3) : deriv (fun a=>superposedMagnetic r k R Q u (x,y,a) i) z=
      (PhysicalFourier.factor:ℂ)*∫q in disk r,magneticPartial k R Q u 2 ((x,y,z),q) i :=
    (superposed_partial r k R Q u hu (x,y,z) 2 i).2.deriv
  have hi (j i:Fin 3) := (partial_integrable r k R Q u hu (x,y,z) j i).2
  ext i;fin_cases i
  · simp [curl,partialCurl,hx,hy,hz]
    rw [integral_sub (hi 1 2) (hi 2 1)];ring
  · simp [curl,partialCurl,hx,hy,hz]
    rw [integral_sub (hi 2 0) (hi 0 2)];ring
  · simp [curl,partialCurl,hx,hy,hz]
    rw [integral_sub (hi 0 1) (hi 1 0)];ring

theorem constitutive_integral (r:ℝ) (R Q:ObliqueVacuum.RMat) (F:Transverse→Vec3)
    (hF:∀i,IntegrableOn (fun q=>F q i) (disk r)) (c:ℂ) :
    (fun i=>c*∫q in disk r,constitutive R Q (F q) i)=constitutive R Q (fun i=>c*∫q in disk r,F q i) := by
  ext i;fin_cases i
  · simp [constitutive,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    rw [integral_add ((hF 0).const_mul _) ((hF 1).const_mul _),integral_const_mul,integral_const_mul];ring
  · simp [constitutive,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    rw [integral_add ((hF 0).const_mul _) ((hF 1).const_mul _),integral_const_mul,integral_const_mul];ring
  · rfl

/-- Genuine classical three-dimensional Maxwell equations for the actual compact
angular-spectrum material fields, using physical κ and the unitary 1/(2π) convention. -/
theorem superposed_maxwell (r k:ℝ) (hk:k≠0) (R Q:ObliqueVacuum.RMat)
    (u:Transverse→ObliqueMaxwell.Channel→ℂ) (hu:ContinuousOn u (disk r)) (x y z:ℝ) :
    curl (fun x y z=>superposedElectric r k R Q u (x,y,z)) x y z=
      (Complex.I*(k:ℂ)) • superposedMagnetic r k R Q u (x,y,z) ∧
    curl (fun x y z=>superposedMagnetic r k R Q u (x,y,z)) x y z=
      (-(Complex.I*(k:ℂ))) • constitutive R Q (superposedElectric r k R Q u (x,y,z)) := by
  rw [curl_integral_electric r k R Q u hu,curl_integral_magnetic r k R Q u hu]
  have he : (fun i=>(PhysicalFourier.factor:ℂ)*∫q in disk r,partialCurl (fun j=>electricPartial k R Q u j ((x,y,z),q)) i)=
      (Complex.I*(k:ℂ)) • superposedMagnetic r k R Q u (x,y,z) := by
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,superposedMagnetic]
    rw [show (fun q=>partialCurl (fun j=>electricPartial k R Q u j ((x,y,z),q)) i)=
      (fun q=>(Complex.I*(k:ℂ))*magneticPlane k R Q u ((x,y,z),q) i) from
      funext (fun q=>congrFun (pointwise_maxwell k hk R Q u (x,y,z) q).1 i),integral_const_mul]
    ring
  have hm : (fun i=>(PhysicalFourier.factor:ℂ)*∫q in disk r,partialCurl (fun j=>magneticPartial k R Q u j ((x,y,z),q)) i)=
      (-(Complex.I*(k:ℂ))) • constitutive R Q (superposedElectric r k R Q u (x,y,z)) := by
    have hi := constitutive_integral r R Q (fun q=>electricPlane k R Q u ((x,y,z),q))
      (fun i=>(plane_integrable r k R Q u hu (x,y,z) i).1) (PhysicalFourier.factor:ℂ)
    ext i
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [show (fun q=>partialCurl (fun j=>magneticPartial k R Q u j ((x,y,z),q)) i)=
      (fun q=>(-(Complex.I*(k:ℂ)))*constitutive R Q (electricPlane k R Q u ((x,y,z),q)) i) from
      funext (fun q=>congrFun (pointwise_maxwell k hk R Q u (x,y,z) q).2 i),integral_const_mul]
    change _ = -(Complex.I*(k:ℂ))*constitutive R Q (fun i=>(PhysicalFourier.factor:ℂ)*∫q in disk r,electricPlane k R Q u ((x,y,z),q) i) i
    rw [←congrFun hi i]
    ring
  exact ⟨he,hm⟩

end GeneralizedResearch.MaxwellIntegrals
