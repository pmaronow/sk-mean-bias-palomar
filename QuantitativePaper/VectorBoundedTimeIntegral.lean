module
public import QuantitativePaper.VectorItoTimeExpectation

@[expose] public section

/-! Literal Fubini and integrability for uniformly bounded measurable
space-time sources on the actual vector Wiener probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 400000

theorem vectorBoundedTimeIntegral_fubini {n : ℕ}
    (w : ℝ≥0→VectorDisorderBrownianSample n→ℝ)
    (hw : Measurable (Function.uncurry w)) (T K : ℝ≥0)
    (hb : ∀r≤T,∀sample,‖w r sample‖≤K) :
    Integrable (Function.uncurry w)
      ((nonnegativeLebesgueMeasure.restrict (Ioc 0 T)).prod (vectorDisorderBrownianMeasure n)) ∧
    (∫ sample,(∫ r in Ioc 0 T,w r sample ∂nonnegativeLebesgueMeasure)
      ∂vectorDisorderBrownianMeasure n)=
      ∫ r in Ioc 0 T,(∫ sample,w r sample ∂vectorDisorderBrownianMeasure n)
        ∂nonnegativeLebesgueMeasure := by
  let μ := nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) T)
  haveI : IsFiniteMeasure μ := ⟨by
    simpa only [μ,Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)⟩
  have hbound : ∀ᵐz ∂μ.prod (vectorDisorderBrownianMeasure n),‖w z.1 z.2‖≤K := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hw.norm measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Eventually.of_forall (hb r hr.2)
  have hi : Integrable (Function.uncurry w) (μ.prod (vectorDisorderBrownianMeasure n)) :=
    (integrable_const (K : ℝ)).mono' hw.aestronglyMeasurable hbound
  refine ⟨hi,?_⟩
  exact (integral_integral_swap hi).symm

theorem integrableOn_vectorBoundedTimeIntegral_path {n : ℕ}
    (w : ℝ≥0→VectorDisorderBrownianSample n→ℝ)
    (hw : Measurable (Function.uncurry w)) (T K : ℝ≥0)
    (hb : ∀r≤T,∀sample,‖w r sample‖≤K) (sample : VectorDisorderBrownianSample n) :
    IntegrableOn (fun r => w r sample) (Ioc 0 T) nonnegativeLebesgueMeasure := by
  apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T) (C := (K : ℝ))).mono'
    hw.of_uncurry_right.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hb r hr.2 sample

end QuantitativePaper
