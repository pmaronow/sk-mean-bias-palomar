module
public import QuantitativePaper.VectorBoundedTimeIntegral

@[expose] public section

/-! Actual Bochner Fubini and integrability on arbitrary bounded physical
time cells in the genuine vector Wiener probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 400000

theorem integrable_vectorBoundedCellIntegral {n : ℕ}
    (w : ℝ≥0→VectorDisorderBrownianSample n→ℝ)
    (hw : Measurable (Function.uncurry w)) (a b K : ℝ≥0)
    (hb : ∀r,∀sample,‖w r sample‖≤K) :
    Integrable (fun sample => ∫r in Ioc a b,w r sample ∂nonnegativeLebesgueMeasure)
      (vectorDisorderBrownianMeasure n) := by
  let μ := nonnegativeLebesgueMeasure.restrict (Ioc a b)
  haveI : IsFiniteMeasure μ := ⟨by
    simpa only [μ,Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top a b)⟩
  have hi : Integrable (Function.uncurry w) (μ.prod (vectorDisorderBrownianMeasure n)) :=
    (integrable_const (K : ℝ)).mono' hw.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z=>hb z.1 z.2))
  exact hi.integral_prod_right

end QuantitativePaper
