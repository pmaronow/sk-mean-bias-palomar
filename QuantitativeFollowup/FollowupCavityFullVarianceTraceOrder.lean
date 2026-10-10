module
public import QuantitativeFollowup.FollowupCavityStableTrace

@[expose] public section

/-! The exact source quadratic-order assumption controls the actual scaled
rest trace. This also covers stability beyond the reference-error criterion. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem followupCavity_scaled_trace_le_of_quadratic_order (n : ℕ) (hn : 0 < n)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (hone : parisiFreeMeasure μ a {(1 : Paper.Overlap)} = 0)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) (ρ/4))
    (hJ : ∀ f : endpointFixedL2 (parisiFreeMeasure μ a),
      inner ℝ f (scalarResponseL2Operator (followupCavityScalarBeta n β ρ)
        (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ a ha hμ f) ≤ (1+ε)*‖f‖^2) :
    followupCavityAlpha n β ρ / followupCavityD n β ρ *
      followupCavityTraceMinus n β ρ hβ hρ μ a ha hμ ≤
      (1-3*ρ/4) * followupCavityVarianceMinus n β ρ hβ hρ μ a := by
  have ht := cavityRestResponseTrace_le_of_quadratic_order
    (followupCavityRestSpinModel n β ρ hβ hρ) (followupCavityScalarBeta n β ρ)
    (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ a ha hμ hone (1+ε) hJ
  have hα := followupCavityAlpha_div_D_mem_contraction_interval hn β ρ hβ hρ
  have hg := followupCavity_effective_response_gap_three_quarters n hn β ρ hβ hρ ε hε
  have hv := cavityRestVariance_nonneg (followupCavityRestSpinModel n β ρ hβ hρ) μ a
  calc
    _ ≤ (followupCavityAlpha n β ρ / followupCavityD n β ρ) *
        ((1+ε)*followupCavityVarianceMinus n β ρ hβ hρ μ a) :=
      mul_le_mul_of_nonneg_left ht hα.1
    _ = (followupCavityAlpha n β ρ / followupCavityD n β ρ*(1+ε))*
        followupCavityVarianceMinus n β ρ hβ hρ μ a := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hg hv

end QuantitativeFollowup
