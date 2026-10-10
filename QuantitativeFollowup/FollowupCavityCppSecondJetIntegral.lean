module
public import QuantitativeFollowup.FollowupCavityNativeCppSecondCubic
public import QuantitativeFollowup.FollowupCavityCppTaylorMeasurable

@[expose] public section

/-! Actual closed native jets are measurable in the split. The local cubic
term is integrated against the genuine free profile measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private theorem cppJet_inward_sequence (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    ∃η : ℕ→ℝ, (∀j,η j∈Icc (0:ℝ) 1) ∧
      Tendsto η atTop (𝓝[Icc (0:ℝ) 1\{u}] u) := by
  let δ : ℕ→ℝ:=fun j=>1/((j:ℝ)+1)
  have hδ (j):δ j∈Icc (0:ℝ) 1 := by
    dsimp only [δ]
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α:=ℝ) j])
  have hδ0 (j):δ j≠0:=by dsimp only [δ];positivity
  have htδ : Tendsto δ atTop (𝓝 (0:ℝ)):=tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hu0:u=0
  · subst u
    exact ⟨δ,hδ,tendsto_nhdsWithin_iff.2 ⟨htδ,
      .of_forall fun j=>⟨hδ j,by simpa only [Set.mem_singleton_iff] using hδ0 j⟩⟩⟩
  · let η : ℕ→ℝ:=fun j=>u-u*δ j
    have hη (j):η j∈Icc (0:ℝ) 1 := by
      dsimp only [η]
      constructor
      · nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr (hδ j).2)]
      · nlinarith [mul_nonneg hu.1 (hδ j).1,hu.2]
    have hη0 (j):η j≠u := by
      dsimp only [η]
      intro he
      have hh:u*δ j=0:=by linarith
      exact (mul_ne_zero hu0 (hδ0 j)) hh
    have htη:Tendsto η atTop (𝓝 u) := by
      simpa only [η,mul_zero,sub_zero] using tendsto_const_nhds.sub (htδ.const_mul u)
    exact ⟨η,hη,tendsto_nhdsWithin_iff.2 ⟨htη,
      .of_forall fun j=>⟨hη j,by simpa only [Set.mem_singleton_iff] using hη0 j⟩⟩⟩

theorem measurable_followupCavityCppFunction_withinJet_split
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) (r : ℕ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Measurable (fun p : Paper.Overlap=>
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) r u) := by
  induction r generalizing u with
  | zero => exact measurable_followupCavityCppFunction_split β ρ hβ hρ μ a u hu
  | succ r ih =>
    obtain ⟨η,hη,htη⟩:=cppJet_inward_sequence u hu
    have hm (j):Measurable (fun p : Paper.Overlap=>
      (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) r (η j)-
        withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) r u)/(η j-u)) :=
      ((ih (η j) (hη j)).sub (ih u hu)).div_const _
    apply measurable_of_tendsto_metrizable hm
    apply tendsto_pi_nhds.2
    intro p
    have hd:=hasDerivWithinAt_followupCavityCppFunction_withinJet hn β ρ hβ hρ μ a ha hfloor p r u hu
    have hh:=(hasDerivWithinAt_iff_tendsto_slope.mp hd).comp htη
    simpa only [Function.comp_def,slope_def_field] using hh

theorem integrable_followupCavityCppFunction_secondWithinJet
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun p : Paper.Overlap=>
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 2 u)
      (parisiFreeMeasure μ a) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let K:=(followupCavityAlpha n β ρ/2)^2*cavityCppSecondStreamingCost
  have hi:=((integrable_const (cavityThirdMoment D μ a)).add
    ((integrable_cavityCubicPairMoment D μ a).const_mul 3)).const_mul K
  apply hi.mono'
    (measurable_followupCavityCppFunction_withinJet_split hn β ρ hβ hρ μ a ha hfloor 2 u hu).aestronglyMeasurable
  exact .of_forall fun p=>by
    rw [Real.norm_eq_abs]
    exact abs_followupCavityCppFunction_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor p u hu

theorem integral_norm_followupCavityCppFunction_secondWithinJet_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    (∫p,‖withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 2 u‖
      ∂parisiFreeMeasure μ a)≤β^4*cavityCppSecondStreamingCost*cavityThirdMoment D μ a := by
  dsimp only
  let ν:=parisiFreeMeasure μ a
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let M:=cavityThirdMoment D μ a
  let χ:=cavityCubicPairMoment D μ a
  let K:=(followupCavityAlpha n β ρ/2)^2*cavityCppSecondStreamingCost
  have hK:0≤K:=by dsimp only [K];rw [cavityCppSecondStreamingCost_eq];positivity
  have hM:0≤M:=cavityThirdMoment_nonneg D μ a
  have hiχ:Integrable χ ν:=integrable_cavityCubicPairMoment D μ a
  have hiB:Integrable (fun p=>K*(M+3*χ p)) ν:=
    ((integrable_const M).add (hiχ.const_mul 3)).const_mul K
  have hb:=integral_mono
    (integrable_followupCavityCppFunction_secondWithinJet hn β ρ hβ hρ μ a ha hfloor u hu).norm hiB
    (fun p=>by simpa only [Real.norm_eq_abs,K,M,χ,D] using
      abs_followupCavityCppFunction_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor p u hu)
  have hmass:ν.real univ=1-a:=by
    dsimp only [ν]
    rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
  have hInt:(∫p,K*(M+3*χ p)∂ν)=K*(M*(1-a)+3*M) := by
    rw [integral_const_mul,integral_add (integrable_const M) (hiχ.const_mul 3),
      integral_const,integral_const_mul,hmass,smul_eq_mul]
    change K*((1-a)*M+3*M)=_
    ring
  rw [hInt] at hb
  have hα0:=followupCavityAlpha_nonneg n β ρ hρ.2
  have hα:followupCavityAlpha n β ρ≤β^2 := by
    have hD:=(followupCavityD_window n hn β ρ ⟨hρ.1.le,hρ.2⟩).2
    have hC:0≤followupCavityC β ρ:=by
      unfold followupCavityC
      exact mul_nonneg (sq_nonneg β) hρ.1.le
    rw [followupCavityD] at hD
    linarith
  have hαsq:followupCavityAlpha n β ρ^2≤β^4:=by
    simpa only [←pow_mul] using pow_le_pow_left₀ hα0 hα 2
  calc
    _≤K*(M*(1-a)+3*M):=hb
    _≤4*K*M:=by nlinarith [mul_nonneg ha.1 hM,mul_nonneg hK (mul_nonneg ha.1 hM)]
    _=followupCavityAlpha n β ρ^2*(cavityCppSecondStreamingCost*M):=by dsimp only [K];ring
    _≤β^4*(cavityCppSecondStreamingCost*M):=
      mul_le_mul_of_nonneg_right hαsq (by rw [cavityCppSecondStreamingCost_eq];positivity)
    _=β^4*cavityCppSecondStreamingCost*cavityThirdMoment D μ a:=by dsimp only [M];ring

end QuantitativeFollowup
