module
public import QuantitativePaper.VectorBoundedTimeIntegral
public import StochasticCalculus.QuadraticVariationDensity

@[expose] public section

/-! Exact conversion of the actual nonnegative-time Lebesgue integrals to
real interval integrals, including shifted physical-time intervals. -/
noncomputable section
open MeasureTheory Set StochasticCalculus
open scoped NNReal
namespace QuantitativePaper

theorem vectorNonnegativeTimeIntegral_eq_interval (f : ℝ→ℝ) (hf : Measurable f)
    (T : ℝ≥0) :
    (∫ r in Ioc 0 T,f r ∂nonnegativeLebesgueMeasure)=∫ r in (0 : ℝ)..(T : ℝ),f r := by
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  have hh := integral_map_of_stronglyMeasurable NNReal.continuous_coe.measurable hf.stronglyMeasurable
    (μ := nonnegativeLebesgueMeasure.restrict (Ioc 0 T))
  rw [map_nonnegativeLebesgueMeasure_restrict_Ioc] at hh
  exact hh.symm

theorem vectorNonnegativeTimeIntegral_eq_shifted_interval (f : ℝ→ℝ) (hf : Measurable f)
    (a : ℝ) (T : ℝ≥0) :
    (∫ r in Ioc 0 T,f (a+r) ∂nonnegativeLebesgueMeasure)=∫ r in a..a+(T : ℝ),f r := by
  rw [vectorNonnegativeTimeIntegral_eq_interval (fun r => f (a+r)) (hf.comp (by fun_prop))]
  simpa only [add_zero] using intervalIntegral.integral_comp_add_left f a (a := 0) (b := (T : ℝ))

end QuantitativePaper
