module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments
public import QuantitativeFollowup.ScalarResponseSamples
public import FourPapersCommon.IntegrableBoundedFamilies

@[expose] public section

/-! Every bounded rest observable paired with a literal scalar response
sample is integrable under the genuine complete independent-endpoint law.
The estimate uses the actual scalar exponential envelope. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem integrable_cavityZeroMarked_scalarResponseSample_product
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (F : AnisotropicDisorderBrownianSample n×Configuration n→ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hb : ∀z,‖F z‖≤C)
    (j : Fin 8) (p r l : Paper.Overlap) :
    Integrable (fun z=>F (cavityZeroMarkedSampleSplit n z).1*
      scalarResponseSample j (followupCavityScalarBeta n β ρ) μ p r l
        (cavityZeroMarkedSampleSplit n z).2)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) :=by
  have hmF : Measurable (fun z=>F (cavityZeroMarkedSampleSplit n z).1) :=
    hF.comp (measurable_fst.comp (measurable_cavityZeroMarkedSampleSplit n))
  have hmG : Measurable (fun z=>scalarResponseSample j
      (followupCavityScalarBeta n β ρ) μ p r l (cavityZeroMarkedSampleSplit n z).2) :=
    (measurable_scalarResponseSample j _ (followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
      μ p r l).comp (measurable_snd.comp (measurable_cavityZeroMarkedSampleSplit n))
  apply bounded_real_integrable _ (hmF.mul hmG)
    (C*(1+2*Real.exp ((followupCavityScalarBeta n β ρ)^2)))
  intro z
  simp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul (hb _) (norm_scalarResponseSample_le j _ μ p r l _)
    (norm_nonneg _) hC

end QuantitativeFollowup
