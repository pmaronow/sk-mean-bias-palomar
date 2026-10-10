module
public import QuantitativeFollowup.FollowupCavitySignedResponseT2Original

@[expose] public section

/-! Fixed-level genuine product Fubini for the literal second signed
response term, retaining the true free measure and actual rest law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponseT2Double_eq_iterated (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a B : ℝ) (hB : B≠0) (p : Paper.Overlap) :
    cavitySignedResponseT2Double D μ a B p =
      (1/2 : ℝ) * ∫r, ∫l, cavitySignedScalarKernelTriple B μ (r,l) p *
        (∫sample, cavitySignedResponseSymmetricMeanResidual D μ r l sample *
          cavitySignedResponseCenteredSelfOverlap D μ a p sample
          ∂anisotropicMeasureSampleLaw D μ a)
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a := by
  let P := anisotropicMeasureSampleLaw D μ a
  let Q := fun rl : Paper.Overlap×Paper.Overlap =>
    ∫sample, cavitySignedResponseSymmetricMeanResidual D μ rl.1 rl.2 sample *
      cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂P
  have hA := (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp
    ((measurable_const (a := p)).prodMk (measurable_snd : Measurable
      (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n => z.2)))
  have hQ : Measurable Q :=
    ((measurable_joint_cavitySignedResponseSymmetricMeanResidual D μ).mul hA).stronglyMeasurable.integral_prod_right'.measurable
  have hQb (rl : Paper.Overlap×Paper.Overlap) : ‖Q rl‖≤4 := by
    have hb (sample : AnisotropicDisorderBrownianSample n) :
        ‖cavitySignedResponseSymmetricMeanResidual D μ rl.1 rl.2 sample *
          cavitySignedResponseCenteredSelfOverlap D μ a p sample‖≤4 := by
      rw [norm_mul]
      exact (mul_le_mul
        (norm_cavitySignedResponseMeanResidual_le D μ (min rl.1 rl.2) (max rl.1 rl.2) sample)
        (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p sample)
        (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have H := norm_integral_le_of_norm_le_const (μ := P) (.of_forall hb)
    simpa only [Q,probReal_univ,mul_one] using H
  have hKb (rl : Paper.Overlap×Paper.Overlap) :
      ‖cavitySignedScalarKernelTriple B μ rl p‖≤1 := by
    have hs := cavitySignedScalarKernelTriple_square_le B μ rl.1 rl.2 p
    have hb : Gamma B μ (min rl.1 rl.2) * Gamma B μ p ≤ 1 :=
      (mul_le_mul (scalarGamma_le_one B μ _ (min rl.1 rl.2).property)
        (scalarGamma_le_one B μ p p.property) (scalarGamma_nonneg B μ p) zero_le_one).trans_eq (one_mul (1 : ℝ))
    rw [Real.norm_eq_abs]
    nlinarith [hs.trans hb, sq_abs (cavitySignedScalarKernelTriple B μ rl p),
      abs_nonneg (cavitySignedScalarKernelTriple B μ rl p)]
  have hm : Measurable (fun rl : Paper.Overlap×Paper.Overlap =>
      cavitySignedScalarKernelTriple B μ rl p * Q rl) :=
    ((continuous_cavitySignedScalarKernelTriple B hB μ).measurable.comp
      (measurable_id.prodMk measurable_const)).mul hQ
  have hi : Integrable (fun rl : Paper.Overlap×Paper.Overlap =>
      cavitySignedScalarKernelTriple B μ rl p * Q rl)
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) := by
    apply (integrable_const (c := (4 : ℝ))).mono' hm.aestronglyMeasurable
    exact .of_forall fun rl => by
      rw [norm_mul]
      exact (mul_le_mul (hKb rl) (hQb rl) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  unfold cavitySignedResponseT2Double
  rw [integral_prod _ hi]

end QuantitativeFollowup
