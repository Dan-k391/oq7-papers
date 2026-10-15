import GeneralizedResearch.BeamPhysicalPackets
import GeneralizedResearch.BeamFlux
import GeneralizedResearch.PhysicalBeamL2
import GeneralizedResearch.ActualStackBeamFields

/-! Net Poynting flux of the actual total boundary fields, including cancellation
of incoming/outgoing interference and the physical time-average factor. -/
noncomputable section
namespace GeneralizedResearch.BoundaryFlux
open MeasureTheory Set BeamPackets BeamAveraging BeamFibers PhysicalBeamL2
open ObliqueMaxwell ObliqueWaveBasis TransferScattering
open scoped Matrix
abbrev Transverse := BeamAveraging.Transverse

def totalElectric (k:ℝ) (q:Transverse) (S:Mat4) (u:Channel→ℂ) : Channel→ℂ :=
  Sum.elim (fun i=>(basis k (WithLp.ofLp q)*ᵥ(leftWaves S*ᵥu)) (Sum.inl i))
    (fun i=>(basis k (WithLp.ofLp q)*ᵥ(rightWaves S*ᵥu)) (Sum.inl i))

def totalMagnetic (k:ℝ) (q:Transverse) (S:Mat4) (u:Channel→ℂ) : Channel→ℂ :=
  Sum.elim (fun i=>(basis k (WithLp.ofLp q)*ᵥ(leftWaves S*ᵥu)) (Sum.inr i))
    (fun i=>-(basis k (WithLp.ofLp q)*ᵥ(rightWaves S*ᵥu)) (Sum.inr i))

theorem total_boundary_coordinates (k:ℝ) (q:Transverse) (S:Mat4) (u:Channel→ℂ) :
    totalElectric k q S u=BeamFlux.electricMatrix k q*ᵥ(u+S*ᵥu) ∧
      totalMagnetic k q S u=BeamFlux.magneticMatrix k q*ᵥ(u-S*ᵥu) := by
  constructor <;> ext i <;> rcases i with i|i <;> fin_cases i
  all_goals simp [totalElectric,totalMagnetic,BeamFlux.electricMatrix,BeamFlux.magneticMatrix,
    basis,leftWaves,rightWaves,Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two]
  all_goals ring

theorem real_interference_cancel {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u v:E) :
    (inner ℂ (u+v) (u-v)).re=‖u‖^2-‖v‖^2 := by
  have hs := inner_re_symm (𝕜:=ℂ) u v
  change (inner ℂ u v).re=(inner ℂ v u).re at hs
  have hself (w:E) : (inner ℂ w w).re=‖w‖^2 := by
    simp [inner_self_eq_norm_sq_to_K,pow_two,Complex.mul_re]
  simp only [inner_add_left,inner_sub_right,Complex.add_re,Complex.sub_re,hself]
  linarith

theorem coordinates_interference_cancel (u v:Channel→ℂ) :
    (inner ℂ (FiniteHilbertBridge.vector (u+v)) (FiniteHilbertBridge.vector (u-v))).re=
      ChannelPowers.power u-ChannelPowers.power v := by
  change (inner ℂ (FiniteHilbertBridge.vector u+FiniteHilbertBridge.vector v)
    (FiniteHilbertBridge.vector u-FiniteHilbertBridge.vector v)).re=_
  rw [real_interference_cancel,FiniteHilbertBridge.norm_sq_coordinates,FiniteHilbertBridge.norm_sq_coordinates]
  rfl

def electricField (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :=
  let hout := d.output_continuousOn u hu
  let hE := packet_memLp d.r _ (BeamFlux.field_continuousOn d.k d.r d.hk (by linarith [d.hrk,d.hk])
    (fun q=>u q+d.S q*ᵥu q) (hu.add hout)).1
  (Real.sqrt 2:ℂ) • PhysicalFourier.inverse (hE.toLp (packet d.r
    (fun q=>BeamFlux.electric d.k q (u q+d.S q*ᵥu q))))

def magneticField (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :=
  let hout := d.output_continuousOn u hu
  let hH := packet_memLp d.r _ (BeamFlux.field_continuousOn d.k d.r d.hk (by linarith [d.hrk,d.hk])
    (fun q=>u q-d.S q*ᵥu q) (hu.sub hout)).2
  (Real.sqrt 2:ℂ) • PhysicalFourier.inverse (hH.toLp (packet d.r
    (fun q=>BeamFlux.magnetic d.k q (u q-d.S q*ᵥu q))))

/-- The real physical E/H flux of the total boundary fields equals actual
incoming minus outgoing power. The right boundary uses the inward orientation. -/
theorem net_physical_flux (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    (1/2:ℝ)*(inner ℂ (electricField d u hu) (magneticField d u hu)).re=
      ‖beam d.r u hu‖^2-‖beam d.r (fun q=>d.S q*ᵥu q) (d.output_continuousOn u hu)‖^2 := by
  have hE := hu.add (d.output_continuousOn u hu)
  have hH := hu.sub (d.output_continuousOn u hu)
  have hf := BeamFlux.physical_spatial_flux d.k d.r d.hk d.hr (by linarith [d.hrk,d.hk])
    (fun q=>u q+d.S q*ᵥu q) (fun q=>u q-d.S q*ᵥu q) hE hH
  change (1/2:ℝ)*(inner ℂ (electricField d u hu) (magneticField d u hu)).re=_ at hf
  rw [hf]
  have he : (fun q=>(inner ℂ (FiniteHilbertBridge.vector (u q+d.S q*ᵥu q))
      (FiniteHilbertBridge.vector (u q-d.S q*ᵥu q))).re)=
      fun q=>ChannelPowers.power (u q)-ChannelPowers.power (d.S q*ᵥu q) := by
    funext q;exact coordinates_interference_cancel _ _
  rw [he,average_sub d.r _ _ (power_continuousOn d.r u hu)
    (power_continuousOn d.r _ (d.output_continuousOn u hu)),
    ←beam_norm_sq d.r d.hr u hu,←beam_norm_sq d.r d.hr _ (d.output_continuousOn u hu)]

theorem normalized_net_absorption (d:Design) (u:Transverse→Channel→ℂ)
    (hu:ContinuousOn u (disk d.r)) (hunit:‖beam d.r u hu‖=1) :
    (1/2:ℝ)*(inner ℂ (electricField d u hu) (magneticField d u hu)).re=absorption d u hu := by
  rw [net_physical_flux,hunit]
  simp only [one_pow,PhysicalBeamL2.absorption]


/-- The flux fields are the literal physical inverse angular integrals of
those very total boundary coordinates, rather than unrelated norm variables. -/
theorem total_boundary_integrals_ae (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    ∀ᵐx:Transverse,∀i:Channel,
      electricField d u hu x i=(Real.sqrt 2:ℂ)*((PhysicalFourier.factor:ℂ)*∫q in disk d.r,
        Complex.exp (Complex.I*((inner ℝ q x:ℝ):ℂ))*
          (((Real.sqrt (volume.real (disk d.r)):ℂ)⁻¹)*totalElectric d.k q (d.S q) (u q) i)) ∧
      magneticField d u hu x i=(Real.sqrt 2:ℂ)*((PhysicalFourier.factor:ℂ)*∫q in disk d.r,
        Complex.exp (Complex.I*((inner ℝ q x:ℝ):ℂ))*
          (((Real.sqrt (volume.real (disk d.r)):ℂ)⁻¹)*totalMagnetic d.k q (d.S q) (u q) i)) := by
  have hE := (BeamFlux.field_continuousOn d.k d.r d.hk (by linarith [d.hrk,d.hk])
    (fun q=>u q+d.S q*ᵥu q) (hu.add (d.output_continuousOn u hu))).1
  have hH := (BeamFlux.field_continuousOn d.k d.r d.hk (by linarith [d.hrk,d.hk])
    (fun q=>u q-d.S q*ᵥu q) (hu.sub (d.output_continuousOn u hu))).2
  let fE := PhysicalFourier.inverse ((packet_memLp d.r _ hE).toLp (packet d.r
    (fun q=>BeamFlux.electric d.k q (u q+d.S q*ᵥu q))))
  let fH := PhysicalFourier.inverse ((packet_memLp d.r _ hH).toLp (packet d.r
    (fun q=>BeamFlux.magnetic d.k q (u q-d.S q*ᵥu q))))
  have hefield : electricField d u hu=(Real.sqrt 2:ℂ) • fE := rfl
  have hhfield : magneticField d u hu=(Real.sqrt 2:ℂ) • fH := rfl
  filter_upwards [BeamPhysicalPackets.packet_inverse_coordinates_ae d.r _ hE,
    BeamPhysicalPackets.packet_inverse_coordinates_ae d.r _ hH,
    Lp.coeFn_smul (Real.sqrt 2:ℂ) fE,Lp.coeFn_smul (Real.sqrt 2:ℂ) fH] with x hxE hxH hxEs hxHs
  intro i
  have he (q:Transverse) : BeamFlux.electric d.k q (u q+d.S q*ᵥu q) i=totalElectric d.k q (d.S q) (u q) i :=
    (congrFun (total_boundary_coordinates d.k q (d.S q) (u q)).1 i).symm
  have hh (q:Transverse) : BeamFlux.magnetic d.k q (u q-d.S q*ᵥu q) i=totalMagnetic d.k q (d.S q) (u q) i :=
    (congrFun (total_boundary_coordinates d.k q (d.S q) (u q)).2 i).symm
  constructor
  · rw [hefield,hxEs]
    change (Real.sqrt 2:ℂ)*(fE x i)=_
    rw [show fE x i=_ from hxE i]
    simp only [he]
  · rw [hhfield,hxHs]
    change (Real.sqrt 2:ℂ)*(fH x i)=_
    rw [show fH x i=_ from hxH i]
    simp only [hh]

end GeneralizedResearch.BoundaryFlux
