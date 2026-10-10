module
public import QuantitativeFollowup.AnisotropicOuterProfileConvergence

@[expose] public section

/-! Bounded moving observables under the genuine weak-profile native tilt.
The common Gaussian envelope and the positive normalizer are obtained from
the actual potentials, before passing to the observable integral. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal ENNReal
namespace QuantitativeFollowup
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128

theorem integral_anisotropicMeasureSampleLaw_weighted_Banach
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (F : AnisotropicDisorderBrownianSample n → E) :
    (∫ω,F ω ∂anisotropicMeasureSampleLaw D μ a) =
      ∫ω,anisotropicMeasureOuterWeight D μ a ω.1 • F ω ∂anisotropicBaseWienerLaw n := by
  rw [anisotropicMeasureSampleLaw_density]
  have hm : Measurable (fun ω : AnisotropicDisorderBrownianSample n =>
      ENNReal.ofReal (anisotropicMeasureOuterWeight D μ a ω.1)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_anisotropicMeasureOuterWeight D μ a).comp measurable_fst)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  simp only [ENNReal.toReal_ofReal (anisotropicMeasureOuterWeight_nonneg D μ a _)]

theorem tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I → Paper.ParisiMeasure}
    {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ)
    (F : I → AnisotropicDisorderBrownianSample n → E)
    (G : AnisotropicDisorderBrownianSample n → E)
    (hF : ∀j,AEStronglyMeasurable (F j) (anisotropicBaseWienerLaw n))
    (C : ℝ) (hC : 0≤C) (hb : ∀j ω,‖F j ω‖≤C)
    (hp : ∀ᵐω∂anisotropicBaseWienerLaw n,
      Tendsto (fun j => F j ω) l (𝓝 (G ω))) :
    Tendsto (fun j => ∫ω,F j ω ∂anisotropicMeasureSampleLaw D (μ j) a) l
      (𝓝 (∫ω,G ω ∂anisotropicMeasureSampleLaw D ν a)) := by
  let B := fun ω : AnisotropicDisorderBrownianSample n =>
    (2*anisotropicOuterExponentialEnvelope D ν a ω.1/
      anisotropicMeasureOuterPartition D ν a)*C
  have hB : Integrable B (anisotropicBaseWienerLaw n) :=
    (((integrable_anisotropicOuterExponentialEnvelope D ν a).const_mul 2).div_const _
      |>.comp_fst (vectorBrownianMeasure n)).mul_const C
  have hm (j : I) : AEStronglyMeasurable
      (fun ω : AnisotropicDisorderBrownianSample n =>
        anisotropicMeasureOuterWeight D (μ j) a ω.1 • F j ω)
      (anisotropicBaseWienerLaw n) :=
    ((measurable_anisotropicMeasureOuterWeight D (μ j) a).comp measurable_fst).aestronglyMeasurable.smul (hF j)
  have hbound : ∀ᶠj in l,∀ᵐω∂anisotropicBaseWienerLaw n,
      ‖anisotropicMeasureOuterWeight D (μ j) a ω.1 • F j ω‖≤B ω := by
    filter_upwards [anisotropicMeasureOuterWeight_profile_eventual_bound D hμ a] with j hj
    exact .of_forall fun ω => by
      rw [norm_smul]
      exact mul_le_mul (hj ω.1) (hb j ω) (norm_nonneg _)
        (by unfold anisotropicOuterExponentialEnvelope
            positivity [anisotropicMeasureOuterPartition_pos D ν a])
  have hpoint : ∀ᵐω∂anisotropicBaseWienerLaw n,
      Tendsto (fun j => anisotropicMeasureOuterWeight D (μ j) a ω.1 • F j ω) l
        (𝓝 (anisotropicMeasureOuterWeight D ν a ω.1 • G ω)) := by
    filter_upwards [hp] with ω hω
    exact (tendsto_anisotropicMeasureOuterWeight_profile D hμ a ω.1).smul hω
  have ht := tendsto_integral_filter_of_dominated_convergence B
    (.of_forall hm) hbound hB hpoint
  simpa only [integral_anisotropicMeasureSampleLaw_weighted_Banach] using ht

end QuantitativeFollowup
