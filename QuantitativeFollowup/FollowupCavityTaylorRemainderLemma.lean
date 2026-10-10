module
public import QuantitativeFollowup.FollowupCavityCppSecondJetIntegral
public import QuantitativeFollowup.FollowupCavityCppTaylorCubic

@[expose] public section

/-! Literal two-clause Taylor remainder estimate for the genuine native
covariance curve, with one constant depending only on temperature. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1400000

theorem followup_cavity_taylor_remainder
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) :
    (∀(u : ℝ) (hu : u∈Icc (0:ℝ) 1),
      (∫p,|withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 2 u|
        ∂parisiFreeMeasure μ a)≤
      followupCavityCppTaylorCubicConstant β*cavityThirdMoment
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a) ∧
    |∫p,followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p∂parisiFreeMeasure μ a|≤
      followupCavityCppTaylorCubicConstant β*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ := by
  constructor
  · intro u hu
    have hh:=integral_norm_followupCavityCppFunction_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor u hu
    simp only [Real.norm_eq_abs] at hh
    have hE:1≤Real.exp (21*β^2):=Real.one_le_exp_iff.mpr (by positivity)
    have hM:=cavityThirdMoment_nonneg (followupCavitySpinModel n β ρ hβ hρ u hu) μ a
    have hC:0≤β^4*cavityCppSecondStreamingCost:=by rw [cavityCppSecondStreamingCost_eq];positivity
    have hp:=mul_le_mul_of_nonneg_right hE (mul_nonneg hC hM)
    apply hh.trans
    calc
      β^4*cavityCppSecondStreamingCost*cavityThirdMoment
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a
        ≤Real.exp (21*β^2)*(β^4*cavityCppSecondStreamingCost*cavityThirdMoment
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a):=by simpa only [one_mul] using hp
      _=followupCavityCppTaylorCubicConstant β*cavityThirdMoment
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a:=by
        unfold followupCavityCppTaylorCubicConstant
        ring
  · have hh:=(norm_integral_le_integral_norm
      (followupCavityCppTaylorRemainder n β ρ hβ hρ μ a)).trans
      (integral_norm_followupCavityCppTaylorRemainder_cubic_le hn β ρ hβ hρ μ a ha hfloor)
    simpa only [Real.norm_eq_abs] using hh

end QuantitativeFollowup
