module
public import QuantitativePaper.VectorBoundedCellIntegral

@[expose] public section

/-! Actual bounded weighted time-integral estimates on the vector Wiener
space, proved from Bochner integrability and pointwise source inequalities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 600000
variable {n : ℕ}

theorem integrable_vectorBoundedWeightedTimeIntegral
    (w : ℝ≥0→VectorDisorderBrownianSample n→ℝ) (hw : Measurable (Function.uncurry w))
    (K : ℝ≥0) (hb : ∀r sample,‖w r sample‖≤K)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>∫r in Ioc 0 1,Z sample*w r sample ∂nonnegativeLebesgueMeasure)
      (vectorDisorderBrownianMeasure n) := by
  apply integrable_vectorBoundedCellIntegral _ ((hZ.comp measurable_snd).mul hw) 0 1 (C*K)
  intro r sample
  change ‖Z sample*w r sample‖≤(C*K : ℝ≥0)
  rw [norm_mul,NNReal.coe_mul]
  exact mul_le_mul (hC sample) (hb r sample) (norm_nonneg _) C.coe_nonneg

theorem vectorBoundedSource_expected_weighted_integral_norm_le
    (w : ℝ≥0→VectorDisorderBrownianSample n→ℝ)
    (Z : VectorDisorderBrownianSample n→ℝ) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C)
    (g : ℝ≥0→ℝ) (hgi : IntegrableOn g (Ioc 0 1) nonnegativeLebesgueMeasure)
    (hgb : ∀r∈Ioc (0 : ℝ≥0) 1,∀sample,‖w r sample‖≤g r) :
    ‖∫sample,(∫r in Ioc 0 1,Z sample*w r sample ∂nonnegativeLebesgueMeasure)
      ∂vectorDisorderBrownianMeasure n‖≤(C : ℝ)*(∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure) := by
  have hgn : 0≤∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro r hr
    exact (norm_nonneg (w r (Classical.choice (inferInstance : Nonempty (VectorDisorderBrownianSample n))))).trans
      (hgb r hr _)
  have hs (sample : VectorDisorderBrownianSample n) :
      ‖∫r in Ioc 0 1,Z sample*w r sample ∂nonnegativeLebesgueMeasure‖≤
        (C : ℝ)*(∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure) := by
    rw [integral_const_mul,norm_mul]
    exact mul_le_mul (hC sample)
      (norm_integral_le_of_norm_le hgi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hgb r hr sample)) (norm_nonneg _) C.coe_nonneg
  have hh := norm_integral_le_of_norm_le_const (μ := vectorDisorderBrownianMeasure n)
    (f := fun sample=>∫r in Ioc 0 1,Z sample*w r sample ∂nonnegativeLebesgueMeasure)
    (Eventually.of_forall hs)
  simpa only [probReal_univ,mul_one] using hh

theorem vectorBoundedSource_expected_weighted_integral_le
    (w : ℝ≥0→VectorDisorderBrownianSample n→ℝ) (hw : Measurable (Function.uncurry w))
    (K : ℝ≥0) (hb : ∀r sample,‖w r sample‖≤K)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) (hZn : ∀sample,0≤Z sample)
    (g : ℝ≥0→ℝ) (hgi : IntegrableOn g (Ioc 0 1) nonnegativeLebesgueMeasure)
    (hgn : ∀r∈Ioc (0 : ℝ≥0) 1,0≤g r)
    (hgb : ∀r∈Ioc (0 : ℝ≥0) 1,∀sample,w r sample≤g r) :
    (∫sample,(∫r in Ioc 0 1,Z sample*w r sample ∂nonnegativeLebesgueMeasure)
      ∂vectorDisorderBrownianMeasure n)≤(C : ℝ)*(∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure) := by
  have hi := integrable_vectorBoundedWeightedTimeIntegral w hw K hb Z hZ C hC
  have hgn' : 0≤∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure :=
    setIntegral_nonneg measurableSet_Ioc hgn
  have hs (sample : VectorDisorderBrownianSample n) :
      (∫r in Ioc 0 1,Z sample*w r sample ∂nonnegativeLebesgueMeasure)≤
        (C : ℝ)*(∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure) := by
    have hwi : IntegrableOn (fun r=>w r sample) (Ioc 0 1) nonnegativeLebesgueMeasure := by
      apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1) (C := (K : ℝ))).mono'
        hw.of_uncurry_right.aestronglyMeasurable
      exact Eventually.of_forall (fun r=>hb r sample)
    have hh := setIntegral_mono_on hwi hgi measurableSet_Ioc (fun r hr=>hgb r hr sample)
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hh (hZn sample)).trans
      (mul_le_mul_of_nonneg_right ((le_abs_self (Z sample)).trans (hC sample)) hgn')
  exact (integral_mono hi (integrable_const _) hs).trans_eq (by simp)

end QuantitativePaper
