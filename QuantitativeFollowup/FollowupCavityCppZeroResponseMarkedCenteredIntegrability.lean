module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedSampleIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedProductIntegrability
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap

@[expose] public section

/-! Honest integrability of bounded rest observables times the actual
centered self-overlap, paired with either a scalar sample or a bounded
marked scalar observable. Both whole paths and terminal marks are retained. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

private theorem centeredRest_measurable {n : ℕ} (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1) :=
  ((adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
    ((anisotropicBrownianFiltration n).le _) le_rfl).comp measurable_fst

theorem integrable_cavityZeroMarked_rest_centered_sample
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap)
    (F : AnisotropicDisorderBrownianSample n×Configuration n→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hb : ∀z,‖F z‖≤C) (j : Fin 8) (r l : Paper.Overlap) :
    Integrable (fun z=>F (cavityZeroMarkedSampleSplit n z).1*
      cavitySignedResponseCenteredSelfOverlap (followupCavityRestSpinModel n β ρ hβ hρ)
        μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample j (followupCavityScalarBeta n β ρ) μ p r l
        (cavityZeroMarkedSampleSplit n z).2)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) :=by
  exact integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
    (fun z=>F z*cavitySignedResponseCenteredSelfOverlap
      (followupCavityRestSpinModel n β ρ hβ hρ) μ a p z.1)
    (hF.mul (centeredRest_measurable _ μ a p)) (C*2) (mul_nonneg hC (by norm_num))
    (fun z=>by
      rw [norm_mul]
      exact mul_le_mul (hb z) (norm_cavitySignedResponseCenteredSelfOverlap_le _ μ a p z.1)
        (norm_nonneg _) hC) j p r l

theorem integrable_cavityZeroMarked_rest_centered_product
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap)
    (F : AnisotropicDisorderBrownianSample n×Configuration n→ℝ)
    (G : Paper.BrownianSample×Bool→ℝ) (hF : Measurable F) (hG : Measurable G)
    (C B : ℝ) (hC : 0≤C) (hbF : ∀z,‖F z‖≤C) (hbG : ∀z,‖G z‖≤B) :
    Integrable (fun z=>(F (cavityZeroMarkedSampleSplit n z).1*
      cavitySignedResponseCenteredSelfOverlap (followupCavityRestSpinModel n β ρ hβ hρ)
        μ a p (cavityZeroMarkedSampleSplit n z).1.1)*G (cavityZeroMarkedSampleSplit n z).2)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) :=by
  exact integrable_cavityZeroMarked_bounded_product μ n β ρ hβ hρ a
    (fun z=>F z*cavitySignedResponseCenteredSelfOverlap
      (followupCavityRestSpinModel n β ρ hβ hρ) μ a p z.1) G
    (hF.mul (centeredRest_measurable _ μ a p)) hG (C*2) B (mul_nonneg hC (by norm_num))
    (fun z=>by
      rw [norm_mul]
      exact mul_le_mul (hbF z) (norm_cavitySignedResponseCenteredSelfOverlap_le _ μ a p z.1)
        (norm_nonneg _) hC) hbG

end QuantitativeFollowup
