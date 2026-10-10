module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedLaw

@[expose] public section

/-! Genuine scalar/rest factorization of arbitrary measurable marked-path
products at the independent endpoint. The complete driving paths and both
terminal spin marks are retained in the proven law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem integral_cavityZeroMarked_product (μ : Paper.ParisiMeasure) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (F : AnisotropicDisorderBrownianSample n×Configuration n→ℝ)
    (G : Paper.BrownianSample×Bool→ℝ) (hF : Measurable F) (hG : Measurable G) :
    (∫p,F (cavityZeroMarkedSampleSplit n p).1*G (cavityZeroMarkedSampleSplit n p).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      (∫p,F p ∂anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)*
        (∫p,G p ∂scalarMarkedSpinLaw (followupCavityScalarBeta n β ρ)
          (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ) :=by
  have hm:Measurable (fun p : (AnisotropicDisorderBrownianSample n×Configuration n)×
      (Paper.BrownianSample×Bool)=>F p.1*G p.2):=
    (hF.comp measurable_fst).mul (hG.comp measurable_snd)
  rw [←integral_map (measurable_cavityZeroMarkedSampleSplit n).aemeasurable hm.aestronglyMeasurable,
    cavityZeroMarkedSampleSplit_law μ n β ρ hβ hρ a,integral_prod_mul]

theorem integral_cavityZeroMarked_centered_product_zero (μ : Paper.ParisiMeasure) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (F : AnisotropicDisorderBrownianSample n×Configuration n→ℝ)
    (G : Paper.BrownianSample×Bool→ℝ) (hF : Measurable F) (hG : Measurable G)
    (hiF : Integrable F (anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a))
    (hiG : Integrable G (scalarMarkedSpinLaw (followupCavityScalarBeta n β ρ)
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ)) :
    (∫p,(F (cavityZeroMarkedSampleSplit n p).1-
        ∫z,F z ∂anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)*
      (G (cavityZeroMarkedSampleSplit n p).2-
        ∫z,G z ∂scalarMarkedSpinLaw (followupCavityScalarBeta n β ρ)
          (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ)
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=0 :=by
  have he := integral_cavityZeroMarked_product μ n β ρ hβ hρ a
    (fun z => F z-∫w,F w ∂anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)
    (fun z => G z-∫w,G w ∂scalarMarkedSpinLaw (followupCavityScalarBeta n β ρ)
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ)
    (hF.sub measurable_const) (hG.sub measurable_const)
  change (∫p,(F (cavityZeroMarkedSampleSplit n p).1-_) *
    (G (cavityZeroMarkedSampleSplit n p).2-_) ∂_) = _ at he
  calc
    _ = (∫z,F z-∫w,F w ∂anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a
      ∂anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)*
      (∫z,G z-∫w,G w ∂scalarMarkedSpinLaw (followupCavityScalarBeta n β ρ)
        (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ
        ∂scalarMarkedSpinLaw (followupCavityScalarBeta n β ρ)
          (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ) :=he
    _ = 0 :=by
      rw [integral_sub hiF (integrable_const _),integral_const,probReal_univ,smul_eq_mul,one_mul,sub_self,zero_mul]

end QuantitativeFollowup
