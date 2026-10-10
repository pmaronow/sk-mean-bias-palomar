module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileColumns
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap

@[expose] public section

/-! Genuine native signed residual moments pass through weak profiles and
moving observation times. Terminal pairings are reduced by the actual
full-past conditional law, before taking a common-driver limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 128

theorem tendsto_cavitySignedResponseSelfOverlap_profile_time {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {p : I→Paper.Overlap} {q : Paper.Overlap}
    (hp : Tendsto p l (𝓝 q)) (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => cavitySignedResponseSelfOverlap D (μ j) (p j) ω) l
      (𝓝 (cavitySignedResponseSelfOverlap D ν q ω)) :=
  (continuous_anisotropicSelectedMeanSquare Finset.univ).tendsto _ |>.comp
    (tendsto_anisotropicProcessMagnetization_profile_time D hμ hp ω)

theorem tendsto_cavitySignedResponseCenteredSelfOverlap_profile_time
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) {p : I→Paper.Overlap} {q : Paper.Overlap}
    (hp : Tendsto p l (𝓝 q)) (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => cavitySignedResponseCenteredSelfOverlap D (μ j) a (p j) ω) l
      (𝓝 (cavitySignedResponseCenteredSelfOverlap D ν a q ω)) := by
  have ht := tendsto_cavityRestCenteredOverlapPath_profile D hμ a ω
  have he (κ : Paper.ParisiMeasure) (t : Paper.Overlap) :
      cavityRestCenteredOverlapPath D κ a ω t=cavitySignedResponseCenteredSelfOverlap D κ a t ω := by
    change cavityRestSelfOverlap D κ t ω-cavityRestOverlapMean D κ a t=_
    rw [cavityRestOverlapMean_apply]
    rfl
  simpa only [Function.comp_def,he] using
    (continuous_eval.tendsto _ |>.comp (ht.prodMk_nhds hp))

theorem tendsto_cavitySignedResponseMeanResidual_profile_time
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {r s : I→Paper.Overlap} {p q : Paper.Overlap}
    (hr : Tendsto r l (𝓝 p)) (hs : Tendsto s l (𝓝 q))
    (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => cavitySignedResponseMeanResidual D (μ j) (r j) (s j) ω) l
      (𝓝 (cavitySignedResponseMeanResidual D ν p q ω)) := by
  apply Tendsto.div_const
  apply tendsto_finset_sum
  intro i _
  have hR := (EuclideanSpace.proj i).continuous.tendsto _ |>.comp
    (tendsto_anisotropicProcessMagnetization_profile_time D hμ hr ω)
  have hS := (EuclideanSpace.proj i).continuous.tendsto _ |>.comp
    (tendsto_anisotropicProcessMagnetization_profile_time D hμ hs ω)
  exact hR.mul (hS.sub hR)

theorem tendsto_cavitySignedResponseSymmetricMeanResidual_profile_time
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {r s : I→Paper.Overlap} {p q : Paper.Overlap}
    (hr : Tendsto r l (𝓝 p)) (hs : Tendsto s l (𝓝 q))
    (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => cavitySignedResponseSymmetricMeanResidual D (μ j) (r j) (s j) ω) l
      (𝓝 (cavitySignedResponseSymmetricMeanResidual D ν p q ω)) :=
  tendsto_cavitySignedResponseMeanResidual_profile_time D hμ (hr.min hs) (hr.max hs) ω

theorem tendsto_cavitySignedResponseSymmetricSelfMoment_profile
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ)
    {r s p : I→Paper.Overlap} {r₀ s₀ p₀ : Paper.Overlap}
    (hr : Tendsto r l (𝓝 r₀)) (hs : Tendsto s l (𝓝 s₀)) (hp : Tendsto p l (𝓝 p₀)) :
    Tendsto (fun j => ∫ω,cavitySignedResponseSymmetricMeanResidual D (μ j) (r j) (s j) ω*
      cavitySignedResponseCenteredSelfOverlap D (μ j) a (p j) ω
        ∂anisotropicMeasureSampleLaw D (μ j) a) l
      (𝓝 (∫ω,cavitySignedResponseSymmetricMeanResidual D ν r₀ s₀ ω*
        cavitySignedResponseCenteredSelfOverlap D ν a p₀ ω
          ∂anisotropicMeasureSampleLaw D ν a)) := by
  refine tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded D hμ a _ _ ?_ 4 (by norm_num) ?_ ?_
  · intro j
    exact ((measurable_cavitySignedResponseMeanResidual D (μ j) _ _).mul
      ((measurable_joint_cavitySignedResponseCenteredSelfOverlap D (μ j) a).of_uncurry_left)).aestronglyMeasurable
  · intro j ω
    rw [norm_mul]
    exact (mul_le_mul (norm_cavitySignedResponseMeanResidual_le D (μ j) _ _ ω)
      (norm_cavitySignedResponseCenteredSelfOverlap_le D (μ j) a _ ω)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · exact .of_forall fun ω =>
      (tendsto_cavitySignedResponseSymmetricMeanResidual_profile_time D hμ hr hs ω).mul
        (tendsto_cavitySignedResponseCenteredSelfOverlap_profile_time D hμ a hp ω)

theorem cavitySignedResponseTerminalSelfMoment_eq_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p : Paper.Overlap) :
    (∫z,cavitySignedResponseTerminalResidual D μ r z*cavitySignedResponseSelfOverlap D μ p z.1
      ∂anisotropicMeasureSpinPathLaw D μ a)=
    ∫ω,cavitySignedResponseMeanResidual D μ r 1 ω*cavitySignedResponseSelfOverlap D μ p ω
      ∂anisotropicMeasureSampleLaw D μ a := by
  exact (cavitySignedResponse_conditional_residual_pairing D μ a r 1 r.property.2 _
    ((adapted_cavitySignedResponseSelfOverlap D μ p).mono
      ((anisotropicBrownianFiltration n).mono (Real.toNNReal_mono p.property.2)) le_rfl).stronglyMeasurable
    1 (by norm_num) (norm_cavitySignedResponseSelfOverlap_le D μ p)).symm

theorem tendsto_cavitySignedResponseTerminalSelfMoment_profile
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ)
    {r p : I→Paper.Overlap} {r₀ p₀ : Paper.Overlap}
    (hr : Tendsto r l (𝓝 r₀)) (hp : Tendsto p l (𝓝 p₀)) :
    Tendsto (fun j => ∫z,cavitySignedResponseTerminalResidual D (μ j) (r j) z*
      cavitySignedResponseSelfOverlap D (μ j) (p j) z.1
        ∂anisotropicMeasureSpinPathLaw D (μ j) a) l
      (𝓝 (∫z,cavitySignedResponseTerminalResidual D ν r₀ z*cavitySignedResponseSelfOverlap D ν p₀ z.1
        ∂anisotropicMeasureSpinPathLaw D ν a)) := by
  simp_rw [cavitySignedResponseTerminalSelfMoment_eq_native]
  refine tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded D hμ a _ _ ?_ 2 (by norm_num) ?_ ?_
  · intro j
    exact ((measurable_cavitySignedResponseMeanResidual D (μ j) _ _).mul
      ((measurable_joint_cavitySignedResponseSelfOverlap D (μ j)).of_uncurry_left)).aestronglyMeasurable
  · intro j ω
    rw [norm_mul]
    exact (mul_le_mul (norm_cavitySignedResponseMeanResidual_le D (μ j) _ _ ω)
      (norm_cavitySignedResponseSelfOverlap_le D (μ j) _ ω)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · exact .of_forall fun ω =>
      (tendsto_cavitySignedResponseMeanResidual_profile_time D hμ hr tendsto_const_nhds ω).mul
        (tendsto_cavitySignedResponseSelfOverlap_profile_time D hμ hp ω)

end QuantitativeFollowup
