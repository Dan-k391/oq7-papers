import GeneralizedResearch.PlanarRealization
import GeneralizedResearch.DiagonalAbsorber
import PrescribedExtinction.PlanarSlabStrictAbsorption

/-! Exact normal-incidence Maxwell realization and sharp limits from original
Proposition 6.4. The material geometry is laterally infinite. No finite-power
beam or compact-body conclusion is inferred from the four-port calculation. -/

noncomputable section
namespace GeneralizedResearch.PlanarSharpness
open OQ7Prescribed PlanarRealization Filter
open scoped Matrix Topology

def difference (k η h t : ℝ) : ℝ :=
  |ChannelPowers.absorption (response k η h t) PlanarFourPort.left-
    ChannelPowers.absorption (response k η h t)
      (ChannelPowers.reverse (PlanarFourPort.reference (phase k h)) PlanarFourPort.left)|

theorem difference_formula (k η h : ℝ) (hk : 0<k) (hη : 0≤η) (hh : 0≤h)
    (t : ℝ) (ht0 : -1≤t) (ht1 : t≤1) :
    difference k η h t=(1-t^2)*OQ7.absorptanceLeft (slabR k η h) (slabT k η h) := by
  have ha := physical_power_values k η h t ht0 ht1
  have hn := (OQ7.passive_absorptances_nonneg
    (dielectricSlab_passive k hk 1 η h le_rfl hη hh)).1
  change 0≤OQ7.absorptanceLeft (slabR k η h) (slabT k η h) at hn
  have hcoef : 0≤1-t^2 := by nlinarith
  rw [difference,ha.1,ha.2,zero_sub,abs_neg,abs_of_nonneg (mul_nonneg hcoef hn)]

theorem difference_strict_bounds (k η h : ℝ) (hk : 0<k) (hη : 0<η) (hh : 0<h)
    (t : ℝ) (ht0 : -1<t) (ht1 : t<1) :
    0<difference k η h t ∧ difference k η h t<1-t^2 := by
  rw [difference_formula k η h hk hη.le hh.le t ht0.le ht1.le]
  have hb := dielectricSlab_absorptance_strict_bounds k hk 1 η h le_rfl hη hh
  change 0<OQ7.absorptanceLeft (slabR k η h) (slabT k η h) ∧
    OQ7.absorptanceLeft (slabR k η h) (slabT k η h)<1 at hb
  have hcoef : 0<1-t^2 := by nlinarith
  exact ⟨mul_pos hcoef hb.1,by nlinarith⟩

/-- Both loss and width vary in this actual Maxwell sequence. The exact
η=1/(m+1), kh=(m+1)² slab limit was proved separately from its transfer formula. -/
theorem difference_tendsto (k : ℝ) (hk : 0<k) (t : ℝ) (ht0 : -1≤t) (ht1 : t≤1) :
    Tendsto (fun m => difference k (DiagonalAbsorber.loss m) (DiagonalAbsorber.width k m) t)
      atTop (𝓝 (1-t^2)) := by
  have hc : Tendsto (fun _ : ℕ => 1-t^2) atTop (𝓝 (1-t^2)) := tendsto_const_nhds
  have h := hc.mul (DiagonalAbsorber.absorptance_tendsto hk)
  simp only [mul_one] at h
  convert h using 1
  funext m
  exact difference_formula k _ _ hk (DiagonalAbsorber.loss_pos m).le
    (DiagonalAbsorber.width_pos hk m).le t ht0 ht1

/-- All differences in the actual two-layer family with the specified caps.
The plate index j determines the actual width and real principal eigenvalue;
`PlanarRealization` proves its response for every illumination. -/
def attainable (k P Q X : ℝ) : Set ℝ :=
  {d | ∃ (η h : ℝ) (j : ℕ), 0<η ∧ η≤Q ∧ 0<h ∧ 1≤j ∧
    plateDesignPermittivity j≤P ∧ d=difference k η h (1-X/2)}

theorem attainable_nonempty (k P Q X : ℝ) (hP : 1<P) (hQ : 0<Q) :
    (attainable k P Q X).Nonempty := by
  obtain ⟨j,hj,hcap⟩ := exists_plateDesign_within_cap P hP
  exact ⟨difference k (Q/2) 1 (1-X/2),Q/2,1,j,by positivity,by linarith,
    by norm_num,hj,hcap,rfl⟩

/-- Fixed-extinction sharpness within the physically realized planar class,
with arbitrary P>1 and Q>0. Both incident directions have exactly the stated
extinction, by `physical_extinction_values`, at every member of the sequence. -/
theorem fixed_extinction_supremum (k P Q X : ℝ) (hk : 0<k) (hP : 1<P) (hQ : 0<Q)
    (hX0 : 0<X) (hX4 : X<4) : sSup (attainable k P Q X)=X-X^2/4 := by
  let t := 1-X/2
  have ht0 : -1<t := by dsimp [t]; linarith
  have ht1 : t<1 := by dsimp [t]; linarith
  have hpar : 1-t^2=X-X^2/4 := by dsimp [t]; ring
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (attainable_nonempty k P Q X hP hQ)
  · intro d hd
    obtain ⟨η,h,j,hη,hηQ,hh,hj,hcap,rfl⟩ := hd
    exact ((difference_strict_bounds k η h hk hη hh t ht0 ht1).2.trans_eq hpar).le
  · intro b hb
    obtain ⟨j,hj,hcap⟩ := exists_plateDesign_within_cap P hP
    have hconv := difference_tendsto k hk t ht0.le ht1.le
    rw [hpar] at hconv
    have he := (DiagonalAbsorber.loss_eventually_below hQ).and (hconv.eventually_const_lt hb)
    obtain ⟨m,hmQ,hmb⟩ := he.exists
    refine ⟨difference k (DiagonalAbsorber.loss m) (DiagonalAbsorber.width k m) t,?_,hmb⟩
    exact ⟨_,_,j,DiagonalAbsorber.loss_pos m,hmQ.le,
      DiagonalAbsorber.width_pos hk m,hj,hcap,rfl⟩

/-- A positive integrated tensor-loss budget does not prevent one exact zero
absorption direction: the absorber loss is semidefinite and annihilates y.
This is an actual two-layer field response, with a lossy x channel and a
lossless real plate, not a hypothetical passive matrix alone. -/
theorem positive_budget_zero_absorption (k P Q M : ℝ) (hk : 0<k) (hP : 1<P)
    (hQ : 0<Q) (hM : 0<M) (t : ℝ) (ht0 : -1<t) (ht1 : t<1) :
    ∃ (η h : ℝ) (j : ℕ), 0<η ∧ η≤Q ∧ 0<h ∧ 1≤j ∧
      plateDesignPermittivity j≤P ∧ η*h=M ∧
      ChannelPowers.absorption (response k η h t) PlanarFourPort.left=0 ∧
      0<ChannelPowers.absorption (response k η h t)
        (ChannelPowers.reverse (PlanarFourPort.reference (phase k h)) PlanarFourPort.left) := by
  obtain ⟨j,hj,hcap⟩ := exists_plateDesign_within_cap P hP
  let η := Q/2
  let h := M/η
  have hη : 0<η := by dsimp [η]; positivity
  have hh : 0<h := div_pos hM hη
  have hp := physical_power_values k η h t ht0.le ht1.le
  have ha := (difference_strict_bounds k η h hk hη hh t ht0 ht1).1
  rw [difference_formula k η h hk hη.le hh.le t ht0.le ht1.le,← hp.2] at ha
  refine ⟨η,h,j,hη,by dsimp [η]; linarith,hh,hj,hcap,?_,hp.1,ha⟩
  dsimp [h]
  field_simp [hη.ne']

def relative (k η h t : ℝ) : ℝ := difference k η h t/(2*(1-t))

theorem relative_formula (k η h : ℝ) (hk : 0<k) (hη : 0≤η) (hh : 0≤h)
    (t : ℝ) (ht0 : -1≤t) (ht1 : t<1) :
    relative k η h t=((1+t)/2)*OQ7.absorptanceLeft (slabR k η h) (slabT k η h) := by
  rw [relative,difference_formula k η h hk hη hh t ht0 ht1.le]
  field_simp [(sub_pos.mpr ht1).ne']
  ring

def angleParameter (m : ℕ) : ℝ := 1-DiagonalAbsorber.loss m

theorem angleParameter_bounds (m : ℕ) : 0≤angleParameter m ∧ angleParameter m<1 := by
  have hn : 1≤DiagonalAbsorber.N m := by dsimp [DiagonalAbsorber.N]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hl : DiagonalAbsorber.loss m≤1 := by
    dsimp [DiagonalAbsorber.loss]
    exact (div_le_one (DiagonalAbsorber.N_pos m)).mpr hn
  dsimp [angleParameter]
  exact ⟨by linarith,by linarith [DiagonalAbsorber.loss_pos m]⟩

theorem relative_tendsto (k : ℝ) (hk : 0<k) :
    Tendsto (fun m => relative k (DiagonalAbsorber.loss m) (DiagonalAbsorber.width k m) (angleParameter m))
      atTop (𝓝 (1:ℝ)) := by
  have ht : Tendsto angleParameter atTop (𝓝 (1:ℝ)) := by
    change Tendsto (fun m => 1-DiagonalAbsorber.loss m) atTop (𝓝 (1:ℝ))
    simpa using tendsto_const_nhds.sub DiagonalAbsorber.loss_tendsto
  have hc : Tendsto (fun m => (1+angleParameter m)/2) atTop (𝓝 (1:ℝ)) := by
    convert (tendsto_const_nhds.add ht).div_const 2 using 1
    norm_num
  have h := hc.mul (DiagonalAbsorber.absorptance_tendsto hk)
  simp only [mul_one] at h
  convert h using 1
  funext m
  exact relative_formula k _ _ hk (DiagonalAbsorber.loss_pos m).le
    (DiagonalAbsorber.width_pos hk m).le _
    (by linarith [(angleParameter_bounds m).1]) (angleParameter_bounds m).2

def relativeAttainable (k P Q : ℝ) : Set ℝ :=
  {d | ∃ (η h t : ℝ) (j : ℕ), 0<η ∧ η≤Q ∧ 0<h ∧ -1<t ∧ t<1 ∧ 1≤j ∧
    plateDesignPermittivity j≤P ∧ d=relative k η h t}

/-- With extinction also free, the realized extinction-normalized contrast
has supremum one. The limiting absolute difference simultaneously tends to
zero, as follows from the explicit angle sequence and parabola. -/
theorem relative_supremum (k P Q : ℝ) (hk : 0<k) (hP : 1<P) (hQ : 0<Q) :
    sSup (relativeAttainable k P Q)=1 := by
  obtain ⟨j,hj,hcap⟩ := exists_plateDesign_within_cap P hP
  have hne : (relativeAttainable k P Q).Nonempty :=
    ⟨relative k (Q/2) 1 0,Q/2,1,0,j,by positivity,by linarith,by norm_num,
      by norm_num,by norm_num,hj,hcap,rfl⟩
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt hne
  · intro d hd
    obtain ⟨η,h,t,l,hη,hηQ,hh,ht0,ht1,hl,hcapl,rfl⟩ := hd
    have hgap := (difference_strict_bounds k η h hk hη hh t ht0 ht1).2
    have hden : 0<2*(1-t) := by positivity
    rw [relative,div_le_iff₀ hden]
    nlinarith
  · intro b hb
    have he := (DiagonalAbsorber.loss_eventually_below hQ).and
      ((relative_tendsto k hk).eventually_const_lt hb)
    obtain ⟨m,hmQ,hmb⟩ := he.exists
    refine ⟨relative k (DiagonalAbsorber.loss m) (DiagonalAbsorber.width k m) (angleParameter m),?_,hmb⟩
    exact ⟨_,_,_,j,DiagonalAbsorber.loss_pos m,hmQ.le,DiagonalAbsorber.width_pos hk m,
      by linarith [(angleParameter_bounds m).1],(angleParameter_bounds m).2,hj,hcap,rfl⟩

end GeneralizedResearch.PlanarSharpness
