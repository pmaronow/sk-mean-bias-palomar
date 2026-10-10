module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic

@[expose] public section

/-! A genuine one-sided derivative for a moving family of increments.
The parameter itself need not be differentiable in the family. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1400000

theorem hasDerivWithinAt_moving_increment_zero (H J : ℝ → ℝ → ℝ)
    (B : Set ℝ) (d alpha : ℝ) (hBd : B ∈ 𝓝 d)
    (hcont : ∀ b ∈ B, ContinuousOn (H b) (Icc (0:ℝ) 1))
    (hder : ∀ b ∈ B, ∀ v ∈ Ioo (0:ℝ) 1, HasDerivAt (H b) (J b v) v)
    (hJ : ContinuousAt (fun z : ℝ×ℝ => J z.1 z.2) (d,0)) :
    HasDerivWithinAt (fun u => H (d-alpha*u) u-H (d-alpha*u) 0)
      (J d 0) (Ici (0:ℝ)) 0 := by
  classical
  have hbcont : Continuous (fun u : ℝ=>d-alpha*u) := by fun_prop
  let Good : ℝ → Prop := fun u => u ∈ Ioo (0:ℝ) 1 ∧ d-alpha*u ∈ B
  have hex (u : ℝ) (hu : Good u) : ∃ v ∈ Ioo (0:ℝ) u,
      J (d-alpha*u) v=(H (d-alpha*u) u-H (d-alpha*u) 0)/u := by
    have hc : ContinuousOn (H (d-alpha*u)) (Icc (0:ℝ) u) :=
      (hcont _ hu.2).mono (Icc_subset_Icc le_rfl hu.1.2.le)
    obtain ⟨v,hv,he⟩ := exists_hasDerivAt_eq_slope (H (d-alpha*u))
      (J (d-alpha*u)) hu.1.1 hc (fun v hv=>hder _ hu.2 v ⟨hv.1,hv.2.trans hu.1.2⟩)
    exact ⟨v,hv,by simpa only [sub_zero] using he⟩
  let c : ℝ → ℝ := fun u => if hu : Good u then (hex u hu).choose else 0
  have hgood : ∀ᶠ u in 𝓝[>] (0:ℝ), Good u := by
    have hsmall : ∀ᶠ u in 𝓝[>] (0:ℝ), u < 1 :=
      (show ∀ᶠ u : ℝ in 𝓝 (0:ℝ),u<1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
    have hb : ∀ᶠ u in 𝓝[>] (0:ℝ), d-alpha*u ∈ B := by
      have ht : Tendsto (fun u : ℝ=>d-alpha*u) (𝓝[>] 0) (𝓝 d) := by
        simpa only [mul_zero,sub_zero] using (hbcont.continuousAt (x:=0)).tendsto.mono_left
          nhdsWithin_le_nhds
      exact ht.eventually hBd
    filter_upwards [self_mem_nhdsWithin,hsmall,hb] with u hu hs hbu
    exact ⟨⟨hu,hs⟩,hbu⟩
  have hc0 (u : ℝ) : 0 ≤ c u := by
    dsimp only [c]
    split
    · exact (hex u ‹Good u›).choose_spec.1.1.le
    · exact le_rfl
  have hcu : ∀ᶠ u in 𝓝[>] (0:ℝ), c u ≤ u := by
    filter_upwards [hgood] with u hu
    simp only [c,dif_pos hu]
    exact (hex u hu).choose_spec.1.2.le
  have hct : Tendsto c (𝓝[>] (0:ℝ)) (𝓝 0) :=
    squeeze_zero' (.of_forall hc0) hcu (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hbt : Tendsto (fun u : ℝ=>d-alpha*u) (𝓝[>] (0:ℝ)) (𝓝 d) := by
    simpa only [mul_zero,sub_zero] using (hbcont.continuousAt (x:=0)).tendsto.mono_left
      nhdsWithin_le_nhds
  have hlimit := hJ.tendsto.comp (hbt.prodMk_nhds hct)
  have hslope : Tendsto (fun u : ℝ => (H (d-alpha*u) u-H (d-alpha*u) 0)/u)
      (𝓝[>] (0:ℝ)) (𝓝 (J d 0)) := by
    apply hlimit.congr'
    filter_upwards [hgood] with u hu
    simpa only [Function.comp_def,c,dif_pos hu] using (hex u hu).choose_spec.2
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici (0:ℝ) \ {0}=Ioi 0 := by
    ext u
    simp only [Set.mem_sdiff,mem_Ici,mem_singleton_iff,mem_Ioi]
    constructor
    · intro hu
      exact lt_of_le_of_ne hu.1 (Ne.symm hu.2)
    · intro hu
      exact ⟨hu.le,hu.ne'⟩
  rw [hset]
  have he : slope (fun u=>H (d-alpha*u) u-H (d-alpha*u) 0) 0 =
      fun u=>(H (d-alpha*u) u-H (d-alpha*u) 0)/u := by
    funext u
    rw [slope_def_field]
    simp only [mul_zero,sub_zero,sub_self]
  rw [he]
  exact hslope

end FourPapersCommon
