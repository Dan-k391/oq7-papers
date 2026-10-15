import GeneralizedResearch.BeamFibers
import GeneralizedResearch.PlanarSharpness

/-! Narrow-spectrum exact-extinction tuning for the actual oblique material
family. The integrands are the derived physical scattering observables. -/
noncomputable section
namespace GeneralizedResearch.PhysicalBeamApproximation
open BeamAveraging BeamFibers Set MeasureTheory
open OQ7Prescribed
open scoped Topology

theorem narrow_physical (k η h:ℝ) (j:ℕ) (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j)
    {t0 ε:ℝ} (ht0:-1<t0) (ht1:t0<1) (hε:0<ε) :
    ∃ r,0<r ∧ r≤k/2 ∧ ∃ t,-1<t ∧ t<1 ∧
      diskAverage r (X k η h j t)=2*(1-t0) ∧
        D k η h j t0 0-ε≤diskAverage r (D k η h j t) := by
  have hc := continuousAt_values k η h j hk hη hh hj (t0,0) (by simpa using hk)
  have hd : ContinuousAt (fun t:ℝ=>D k η h j t 0) t0 :=
    ContinuousAt.comp (f:=fun t:ℝ=>(t,(0:BeamAveraging.Transverse))) hc.2
      (continuous_id.prodMk continuous_const).continuousAt
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hd (ε/2) (by positivity)
  let d := min (δ/2) (min ((t0+1)/2) ((1-t0)/2))
  have hd0 : 0<d := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hdδ : d≤δ/2 := min_le_left _ _
  have hdl : d≤(t0+1)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdr : d≤(1-t0)/2 := (min_le_right _ _).trans (min_le_right _ _)
  let a := t0-d
  let b := t0+d
  have ha : a<t0 := by dsimp [a];linarith
  have hb : t0<b := by dsimp [b];linarith
  have ht (t:ℝ) (h:Icc a b t) : -1<t ∧ t<1 := by
    dsimp [a,b] at h
    constructor <;> linarith [h.1,h.2]
  have hX : ContinuousOn (fun z:ℝ×BeamAveraging.Transverse=>X k η h j z.1 z.2)
      (Icc a b ×ˢ Metric.closedBall 0 (k/2)) := by
    intro p hp
    exact ((continuousAt_values k η h j hk hη hh hj p (by
      have hn : ‖p.2‖≤k/2 := by simpa [Metric.mem_closedBall,dist_zero_right] using hp.2
      linarith)).1).continuousWithinAt
  have hD : ContinuousOn (fun z:ℝ×BeamAveraging.Transverse=>D k η h j z.1 z.2)
      (Icc a b ×ˢ Metric.closedBall 0 (k/2)) := by
    intro p hp
    exact ((continuousAt_values k η h j hk hη hh hj p (by
      have hn : ‖p.2‖≤k/2 := by simpa [Metric.mem_closedBall,dist_zero_right] using hp.2
      linarith)).2).continuousWithinAt
  have hnormal : ∀ t∈Icc a b,X k η h j t 0=2*(1-t) := by
    intro t ht'
    exact (normal_values k η h hk hη hh j hj (ht t ht').1.le (ht t ht').2.le).1
  have hvalue : ∀ t∈Icc a b,D k η h j t0 0-ε/2≤D k η h j t 0 := by
    intro t ht'
    have hdist : dist t t0<δ := by
      rw [Real.dist_eq]
      have htd : |t-t0|≤d := abs_le.mpr ⟨by dsimp [a] at ht';linarith [ht'.1],
        by dsimp [b] at ht';linarith [ht'.2]⟩
      linarith
    have hc' := hclose hdist
    have ha' := (abs_lt.mp (show |D k η h j t 0-D k η h j t0 0|<ε/2 by
      simpa only [Real.dist_eq,abs_sub_comm] using hc')).1
    linarith
  obtain ⟨r,hr,hrk,t,ht',hx,hd'⟩ := narrow_exact_target ha hb (by positivity : 0<k/2) hε
    (X k η h j) (D k η h j) hX hD hnormal hvalue
  exact ⟨r,hr,hrk,t,(ht t ht').1,(ht t ht').2,hx,hd'⟩

theorem capped_physical_approach (k P Q X0 ε:ℝ) (hk:0<k) (hP:1<P) (hQ:0<Q)
    (hX0:0<X0) (hX4:X0<4) (hε:0<ε) :
    ∃ (η h:ℝ) (j:ℕ),0<η ∧ η≤Q ∧ 0<h ∧ 1≤j ∧ plateDesignPermittivity j≤P ∧
      ∃ r,0<r ∧ r≤k/2 ∧ ∃ t,-1<t ∧ t<1 ∧
        diskAverage r (X k η h j t)=X0 ∧
          X0-X0^2/4-ε≤diskAverage r (D k η h j t) := by
  let t0 := 1-X0/2
  have ht0 : -1<t0 := by dsimp [t0];linarith
  have ht1 : t0<1 := by dsimp [t0];linarith
  have hpar : 1-t0^2=X0-X0^2/4 := by dsimp [t0];ring
  obtain ⟨j,hj,hcap⟩ := exists_plateDesign_within_cap P hP
  have htend := PlanarSharpness.difference_tendsto k hk t0 ht0.le ht1.le
  rw [hpar] at htend
  have hev := (DiagonalAbsorber.loss_eventually_below hQ).and
    (htend.eventually_const_lt (show X0-X0^2/4-ε/2<X0-X0^2/4 by linarith))
  obtain ⟨m,hmQ,hmb⟩ := hev.exists
  let η := DiagonalAbsorber.loss m
  let h := DiagonalAbsorber.width k m
  have hη : 0<η := DiagonalAbsorber.loss_pos m
  have hh : 0<h := DiagonalAbsorber.width_pos hk m
  obtain ⟨r,hr,hrk,t,htl,htr,hx,hd⟩ := narrow_physical k η h j hk hη.le hh.le hj ht0 ht1
    (show 0<ε/2 by positivity)
  have hDnormal : D k η h j t0 0=PlanarSharpness.difference k η h t0 := by
    rw [(normal_values k η h hk hη.le hh.le j hj ht0.le ht1.le).2,
      PlanarSharpness.difference_formula k η h hk hη.le hh.le t0 ht0.le ht1.le]
  rw [hDnormal] at hd
  refine ⟨η,h,j,hη,hmQ.le,hh,hj,hcap,r,hr,hrk,t,htl,htr,?_,?_⟩
  · calc
      diskAverage r (X k η h j t)=2*(1-t0) := hx
      _ = X0 := by dsimp [t0];ring
  · exact (by linarith : X0-X0^2/4-ε≤diskAverage r (D k η h j t))

end GeneralizedResearch.PhysicalBeamApproximation
