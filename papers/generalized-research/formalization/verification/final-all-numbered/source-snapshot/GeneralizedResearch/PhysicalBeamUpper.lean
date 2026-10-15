import GeneralizedResearch.PhysicalBeamL2

/-! Actual physical L² beam passivity bounds and the relative-one approach. -/
noncomputable section
namespace GeneralizedResearch.PhysicalBeamUpper
open MeasureTheory Set PhysicalBeamL2 BeamAveraging BeamFibers BeamPackets ObliqueFamily
open scoped Matrix
abbrev Transverse := BeamAveraging.Transverse

theorem average_mono (r:ℝ) (hr:0<r) (f g:Transverse→ℝ)
    (hf:ContinuousOn f (disk r)) (hg:ContinuousOn g (disk r)) (hfg:∀q∈disk r,f q≤g q) :
    diskAverage r f≤diskAverage r g := by
  unfold diskAverage BeamAveraging.average
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (disk_mass_pos hr).le)
  apply integral_mono_ae (hf.integrableOn_compact (isCompact_closedBall _ _))
    (hg.integrableOn_compact (isCompact_closedBall _ _))
  filter_upwards [ae_restrict_mem (isCompact_closedBall (0:Transverse) r).measurableSet] with q hq
  exact hfg q hq

theorem output_norm_le (d:Design) (u:Transverse→ObliqueMaxwell.Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    ‖beam d.r (fun q=>d.S q*ᵥu q) (d.output_continuousOn u hu)‖≤‖beam d.r u hu‖ := by
  have hs := average_mono d.r d.hr _ _
    (power_continuousOn d.r _ (d.output_continuousOn u hu)) (power_continuousOn d.r u hu) (fun q hq=>?_) 
  · rw [←beam_norm_sq d.r d.hr _ (d.output_continuousOn u hu),←beam_norm_sq d.r d.hr u hu] at hs
    nlinarith [norm_nonneg (beam d.r u hu),norm_nonneg (beam d.r (fun q=>d.S q*ᵥu q) (d.output_continuousOn u hu))]
  · have hκ : ObliqueVacuum.square (WithLp.ofLp q)<d.k^2 := by
      rw [square_ofLp];nlinarith [d.propagating hq,norm_nonneg q]
    exact ChannelPowers.contraction_power _
      (response_passive d.k d.η d.h d.j _ d.t d.hk d.hη d.hh d.hj hκ) (u q)

theorem background_norm (d:Design) (u:Transverse→ObliqueMaxwell.Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    ‖beam d.r (fun q=>d.S0 q*ᵥu q) (d.background_continuousOn u hu)‖=‖beam d.r u hu‖ := by
  have hs := beam_norm_sq d.r d.hr (fun q=>d.S0 q*ᵥu q) (d.background_continuousOn u hu)
  have he : (fun q=>ChannelPowers.power (d.S0 q*ᵥu q))=(fun q=>ChannelPowers.power (u q)) := by
    funext q;exact ChannelPowers.unitary_power _ (reference_unitary _ _ _) (u q)
  rw [he,←beam_norm_sq d.r d.hr u hu] at hs
  nlinarith [norm_nonneg (beam d.r u hu),norm_nonneg (beam d.r (fun q=>d.S0 q*ᵥu q) (d.background_continuousOn u hu))]

theorem vector_parabola (y b:Wave) (hb:‖b‖=1) (hy:‖y‖≤1) :
    0≤2*(1-(inner ℂ b y).re) ∧ 2*(1-(inner ℂ b y).re)≤4 ∧
      0≤1-‖y‖^2 ∧ 1-‖y‖^2≤2*(1-(inner ℂ b y).re)-(2*(1-(inner ℂ b y).re))^2/4 := by
  have hz := norm_inner_le_norm (𝕜:=ℂ) b y
  rw [hb,one_mul] at hz
  have hr := (Complex.abs_re_le_norm (inner ℂ b y)).trans hz
  have ha := abs_le.mp (hr.trans hy)
  have hs : ((inner ℂ b y).re)^2≤‖y‖^2 := sq_le_sq.mpr (by simpa using hr)
  refine ⟨by linarith,by linarith,?_,?_⟩ <;> nlinarith [norm_nonneg y]

theorem single_input (d:Design) (u:Transverse→ObliqueMaxwell.Channel→ℂ) (hu:ContinuousOn u (disk d.r))
    (hunit:‖beam d.r u hu‖=1) :
    0≤extinction d u hu ∧ extinction d u hu≤4 ∧ 0≤absorption d u hu ∧
      absorption d u hu≤extinction d u hu-(extinction d u hu)^2/4 := by
  have hb := (background_norm d u hu).trans hunit
  have hy := (output_norm_le d u hu).trans_eq hunit
  exact vector_parabola _ _ hb hy

theorem physical_parabola (d:Design) :
    |absorption d d.reverseInput d.reverse_continuous.continuousOn-
      absorption d (fun _=>left) continuousOn_const|≤
        extinction d (fun _=>left) continuousOn_const-(extinction d (fun _=>left) continuousOn_const)^2/4 := by
  have hl := single_input d (fun _=>left) continuousOn_const (left_beam_unit d)
  have hr := single_input d d.reverseInput d.reverse_continuous.continuousOn (reverse_beam_unit d)
  rw [common_extinction] at hr
  exact abs_le.mpr ⟨by linarith [hl.2.2.2,hr.2.2.1],by linarith [hr.2.2.2,hl.2.2.1]⟩

theorem relative_approach (k P Q X0 ε:ℝ) (hk:0<k) (hP:1<P) (hQ:0<Q)
    (hX0:0<X0) (hX4:X0<4) (hε:0<ε) :
    ∃ d:Design,d.k=k ∧ 0<d.η ∧ d.η≤Q ∧ 0<d.h ∧ OQ7Prescribed.plateDesignPermittivity d.j≤P ∧
      -1<d.t ∧ d.t<1 ∧ extinction d (fun _=>left) continuousOn_const=X0 ∧
      1-X0/4-ε≤|absorption d d.reverseInput d.reverse_continuous.continuousOn-
        absorption d (fun _=>left) continuousOn_const|/X0 ∧
      |absorption d d.reverseInput d.reverse_continuous.continuousOn-
        absorption d (fun _=>left) continuousOn_const|/X0≤1-X0/4 := by
  obtain ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,_,_,hx,_,hd⟩ :=
    corollary65_approach k P Q X0 (ε*X0) hk hP hQ hX0 hX4 (mul_pos hε hX0)
  refine ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,hx,?_,?_⟩
  · apply (le_div_iff₀ hX0).mpr
    nlinarith
  · apply (div_le_iff₀ hX0).mpr
    have hu := physical_parabola d
    rw [hx] at hu
    nlinarith


def contrasts (k P Q X0:ℝ) : Set ℝ := {v|∃d:Design,d.k=k ∧ 0<d.η ∧ d.η≤Q ∧
  0<d.h ∧ OQ7Prescribed.plateDesignPermittivity d.j≤P ∧ -1<d.t ∧ d.t<1 ∧
  extinction d (fun _=>left) continuousOn_const=X0 ∧
  v=|absorption d d.reverseInput d.reverse_continuous.continuousOn-
    absorption d (fun _=>left) continuousOn_const|}

theorem corollary65_sSup (k P Q X0:ℝ) (hk:0<k) (hP:1<P) (hQ:0<Q)
    (hX0:0<X0) (hX4:X0<4) : sSup (contrasts k P Q X0)=X0-X0^2/4 := by
  have hn : (contrasts k P Q X0).Nonempty := by
    obtain ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,_,_,hx,_,_⟩ :=
      corollary65_approach k P Q X0 1 hk hP hQ hX0 hX4 (by norm_num)
    exact ⟨_,d,hk',hη,hηQ,hh,hcap,ht0,ht1,hx,rfl⟩
  have hub : ∀v∈contrasts k P Q X0,v≤X0-X0^2/4 := by
    intro v hv
    obtain ⟨d,_,_,_,_,_,_,_,hx,rfl⟩ := hv
    have hu := physical_parabola d
    rwa [hx] at hu
  have hb : BddAbove (contrasts k P Q X0) := ⟨_,hub⟩
  apply le_antisymm (csSup_le hn hub)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,_,_,hx,_,hd⟩ :=
    corollary65_approach k P Q X0 ε hk hP hQ hX0 hX4 hε
  have hm : |absorption d d.reverseInput d.reverse_continuous.continuousOn-
      absorption d (fun _=>left) continuousOn_const|∈contrasts k P Q X0 :=
    ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,hx,rfl⟩
  have hle := le_csSup hb hm
  linarith

theorem relative_one (k P Q ε:ℝ) (hk:0<k) (hP:1<P) (hQ:0<Q) (hε:0<ε) :
    ∃d:Design,d.k=k ∧ 0<d.η ∧ d.η≤Q ∧ 0<d.h ∧ OQ7Prescribed.plateDesignPermittivity d.j≤P ∧
      -1<d.t ∧ d.t<1 ∧ 0<extinction d (fun _=>left) continuousOn_const ∧
      extinction d (fun _=>left) continuousOn_const<ε ∧
      1-ε < |absorption d d.reverseInput d.reverse_continuous.continuousOn-
        absorption d (fun _=>left) continuousOn_const|/extinction d (fun _=>left) continuousOn_const ∧
      |absorption d d.reverseInput d.reverse_continuous.continuousOn-
        absorption d (fun _=>left) continuousOn_const|/extinction d (fun _=>left) continuousOn_const≤1 := by
  let X0 := min 1 (ε/2)
  have hX0 : 0<X0 := lt_min (by norm_num) (by positivity)
  have hX4 : X0<4 := (min_le_left _ _).trans_lt (by norm_num)
  have hXe : X0≤ε/2 := min_le_right _ _
  obtain ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,hx,hl,hu⟩ :=
    relative_approach k P Q X0 (ε/4) hk hP hQ hX0 hX4 (by positivity)
  refine ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,?_,?_,?_,?_⟩ <;> rw [hx]
  · exact hX0
  · linarith
  · linarith
  · linarith

end GeneralizedResearch.PhysicalBeamUpper
