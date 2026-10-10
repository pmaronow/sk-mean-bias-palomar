module
public import QuantitativeFollowup.FollowupCavityContractionAbsorption
public import QuantitativeFollowup.FollowupCavityTraceCovarianceData
public import QuantitativeFollowup.ScalarOperatorStability

@[expose] public section

/-! Actual scalar-reference stability controls the constructed rest covariance
trace, with the source's sharp contraction coefficient. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem followupCavityTraceMinus_le_stability_error (n : ℕ) (hn : 0 < n)
    (β ρ : ℝ) (hβ : 1 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (hone : parisiFreeMeasure μ a {(1 : Paper.Overlap)} = 0) :
    followupCavityTraceMinus n β ρ (zero_lt_one.trans hβ) hρ μ a ha hμ ≤
      (1+scalarOperatorStabilityError β μ (followupCavityD n β ρ)) *
        followupCavityVarianceMinus n β ρ (zero_lt_one.trans hβ) hρ μ a := by
  have hw := followupCavityD_window n hn β ρ ⟨hρ.1.le, hρ.2⟩
  apply cavityRestResponseTrace_le_of_quadratic_order _ _ _ μ a ha hμ hone
  intro f
  simpa only [followupCavityScalarBeta] using
    scalar_reference_operator_stability β hβ μ (followupCavityD n β ρ) hw a ha hμ f

theorem followupCavity_stable_scaled_trace_le (n : ℕ) (hn : 0 < n)
    (β ρ : ℝ) (hβ : 1 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (hone : parisiFreeMeasure μ a {(1 : Paper.Overlap)} = 0)
    (hstable : scalarOperatorStabilityError β μ (followupCavityD n β ρ) ≤ ρ/4) :
    followupCavityAlpha n β ρ / followupCavityD n β ρ *
      followupCavityTraceMinus n β ρ (zero_lt_one.trans hβ) hρ μ a ha hμ ≤
      (1-3*ρ/4) * followupCavityVarianceMinus n β ρ (zero_lt_one.trans hβ) hρ μ a := by
  have ht := followupCavityTraceMinus_le_stability_error n hn β ρ hβ hρ μ a ha hμ hone
  have hα := followupCavityAlpha_div_D_mem_contraction_interval hn β ρ (zero_lt_one.trans hβ) hρ
  have he := scalarOperatorStabilityError_nonneg β (zero_lt_one.trans hβ) μ
    (followupCavityD n β ρ)
  have hg := followupCavity_effective_response_gap_three_quarters n hn β ρ
    (zero_lt_one.trans hβ) hρ (scalarOperatorStabilityError β μ (followupCavityD n β ρ))
    ⟨he, hstable⟩
  have hv := cavityRestVariance_nonneg (followupCavityRestSpinModel n β ρ
    (zero_lt_one.trans hβ) hρ) μ a
  calc
    _ ≤ (followupCavityAlpha n β ρ / followupCavityD n β ρ) *
        ((1+scalarOperatorStabilityError β μ (followupCavityD n β ρ))*
          followupCavityVarianceMinus n β ρ (zero_lt_one.trans hβ) hρ μ a) :=
      mul_le_mul_of_nonneg_left ht hα.1
    _ = (followupCavityAlpha n β ρ / followupCavityD n β ρ *
        (1+scalarOperatorStabilityError β μ (followupCavityD n β ρ))) *
          followupCavityVarianceMinus n β ρ (zero_lt_one.trans hβ) hρ μ a := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hg hv

end QuantitativeFollowup
