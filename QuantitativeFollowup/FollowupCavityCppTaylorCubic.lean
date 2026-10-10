module
public import QuantitativeFollowup.FollowupCavityNativeCppSecondCubic
public import QuantitativeFollowup.FollowupCavityCppTaylorMeasurable
public import QuantitativeFollowup.FollowupCavityCubicSupremum

@[expose] public section

/-! The actual Taylor remainder has an integrated cubic bound. Local split
moments are kept until their genuine free-measure integral is taken. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def followupCavityCppTaylorCubicConstant (β : ℝ) : ℝ :=
  β^4*cavityCppSecondStreamingCost*Real.exp (21*β^2)

theorem followupCavityCppTaylorCubicConstant_nonneg (β : ℝ) :
    0≤followupCavityCppTaylorCubicConstant β := by
  rw [followupCavityCppTaylorCubicConstant,cavityCppSecondStreamingCost_eq]
  positivity

theorem abs_followupCavityCppTaylorRemainder_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) (p : Paper.Overlap) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    |followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p|≤
      (followupCavityAlpha n β ρ/2)^2*cavityCppSecondStreamingCost*Real.exp (21*β^2)*
        (cavityThirdMoment D μ a+3*cavityCubicPairMoment D μ a p) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let M:=cavityThirdMoment D μ a
  let χ:=cavityCubicPairMoment D μ a p
  let K:=(followupCavityAlpha n β ρ/2)^2*cavityCppSecondStreamingCost*Real.exp (21*β^2)
  have hK : 0≤K := by dsimp only [K];rw [cavityCppSecondStreamingCost_eq];positivity
  have hM : 0≤M:=cavityThirdMoment_nonneg D μ a
  have hχ : 0≤χ:=(cavityCubicPairMoment_bounds D μ a p).1
  have hb (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      |withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 2 u|≤K*(M+3*χ) := by
    have hh:=abs_followupCavityCppFunction_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor p u hu
    have hmc:=cavityThirdMoment_comparison hn β ρ hβ hρ μ a ha hfloor u 0 hu ⟨le_rfl,zero_le_one⟩
    have hχc:=cavityCubicPairMoment_comparison hn β ρ hβ hρ μ a ha hfloor p u 0 hu ⟨le_rfl,zero_le_one⟩
    exact (hh.trans (mul_le_mul_of_nonneg_left (show cavityThirdMoment
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a+
        3*cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p≤
        Real.exp (21*β^2)*M+3*(Real.exp (21*β^2)*χ) by
          dsimp only [M,χ,D];linarith)
      (by rw [cavityCppSecondStreamingCost_eq];positivity))).trans_eq (by dsimp only [K];ring)
  have hh:=intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (C:=K*(M+3*χ))
    (f:=fun u=>(1-u)*withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 2 u)
    (fun u hu=>by
      have hu' : u∈Icc (0:ℝ) 1 := by
        have hh : u∈Ioc (0:ℝ) 1:=by simpa only [uIoc_of_le zero_le_one] using hu
        exact ⟨hh.1.le,hh.2⟩
      rw [norm_mul,Real.norm_eq_abs]
      have hw : |1-u|≤1 := by rw [abs_of_nonneg (by linarith [hu'.2])];linarith [hu'.1]
      exact (mul_le_mul hw (by simpa only [Real.norm_eq_abs] using hb u hu')
        (norm_nonneg _) (by positivity)).trans_eq (by ring))
  simpa only [followupCavityCppTaylorRemainder,Real.norm_eq_abs,sub_zero,abs_one,mul_one,K,M,χ,D] using hh

theorem integral_norm_followupCavityCppTaylorRemainder_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) :
    (∫p,‖followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p‖∂parisiFreeMeasure μ a)≤
      followupCavityCppTaylorCubicConstant β*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ := by
  let ν:=parisiFreeMeasure μ a
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let M:=cavityThirdMoment D μ a
  let χ:=cavityCubicPairMoment D μ a
  let K:=(followupCavityAlpha n β ρ/2)^2*cavityCppSecondStreamingCost*Real.exp (21*β^2)
  have hK : 0≤K := by dsimp only [K];rw [cavityCppSecondStreamingCost_eq];positivity
  have hM : 0≤M:=cavityThirdMoment_nonneg D μ a
  have hiR:=(integrable_followupCavityCppTaylorRemainder hn β ρ hβ hρ μ a ha hfloor).norm
  have hiχ:Integrable χ ν:=integrable_cavityCubicPairMoment D μ a
  have hiB:Integrable (fun p=>K*(M+3*χ p)) ν:=
    ((integrable_const M).add (hiχ.const_mul 3)).const_mul K
  have hbound:=integral_mono hiR hiB (fun p=>by
    simpa only [Real.norm_eq_abs,K,M,χ,D] using
      abs_followupCavityCppTaylorRemainder_cubic_le hn β ρ hβ hρ μ a ha hfloor p)
  have hmass:ν.real univ=1-a:=by
    dsimp only [ν]
    rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
  have hInt:(∫p,K*(M+3*χ p)∂ν)=K*(M*(1-a)+3*M) := by
    rw [integral_const_mul,integral_add (integrable_const M) (hiχ.const_mul 3),
      integral_const,integral_const_mul,hmass,smul_eq_mul]
    change K*((1-a)*M+3*M)=_
    ring
  rw [hInt] at hbound
  have hsup:M≤cavityPhysicalCubicSupremum n μ β ρ a hβ hρ:=
    cavityThirdMoment_le_physicalSupremum μ β ρ a hβ hρ ha 0 ⟨le_rfl,zero_le_one⟩
  have hsup0:0≤cavityPhysicalCubicSupremum n μ β ρ a hβ hρ:=
    (cavityPhysicalCubicSupremum_bounds μ β ρ a hβ hρ ha).1
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
    _≤K*(M*(1-a)+3*M):=hbound
    _≤4*K*M:=by nlinarith [mul_nonneg ha.1 hM,mul_nonneg hK (mul_nonneg ha.1 hM)]
    _≤4*K*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ:=
      mul_le_mul_of_nonneg_left hsup (by positivity)
    _=followupCavityAlpha n β ρ^2*
        (cavityCppSecondStreamingCost*Real.exp (21*β^2)*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ):=by
      dsimp only [K];ring
    _≤β^4*(cavityCppSecondStreamingCost*Real.exp (21*β^2)*
        cavityPhysicalCubicSupremum n μ β ρ a hβ hρ):=
      mul_le_mul_of_nonneg_right hαsq (by rw [cavityCppSecondStreamingCost_eq];positivity)
    _=followupCavityCppTaylorCubicConstant β*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ:=by
      unfold followupCavityCppTaylorCubicConstant;ring

end QuantitativeFollowup
