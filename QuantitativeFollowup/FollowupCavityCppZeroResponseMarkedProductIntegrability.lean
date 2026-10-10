module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments
public import FourPapersCommon.IntegrableBoundedFamilies

@[expose] public section

/-! Integrability of genuine independent-endpoint marked products from
their actual bounded sections. This retains both whole paths and spins. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem integrable_cavityZeroMarked_bounded_product
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (F : AnisotropicDisorderBrownianSample n×Configuration n→ℝ)
    (G : Paper.BrownianSample×Bool→ℝ) (hF : Measurable F) (hG : Measurable G)
    (B C : ℝ) (hB : 0≤B) (hbF : ∀z,‖F z‖≤B) (hbG : ∀z,‖G z‖≤C) :
    Integrable (fun z=>F (cavityZeroMarkedSampleSplit n z).1*
      G (cavityZeroMarkedSampleSplit n z).2)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) :=by
  have hmF : Measurable (fun z=>F (cavityZeroMarkedSampleSplit n z).1) :=
    hF.comp (measurable_fst.comp (measurable_cavityZeroMarkedSampleSplit n))
  have hmG : Measurable (fun z=>G (cavityZeroMarkedSampleSplit n z).2) :=
    hG.comp (measurable_snd.comp (measurable_cavityZeroMarkedSampleSplit n))
  apply bounded_real_integrable _ (hmF.mul hmG) (B*C)
  intro z
  simp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul (hbF _) (hbG _) (norm_nonneg _) hB

end QuantitativeFollowup
