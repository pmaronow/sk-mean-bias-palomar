module
public import QuantitativeFollowup.StieltjesLipschitz
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-! Genuine identification of a locally absolutely continuous monotone
Stieltjes primitive with the measure of its actual derivative. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup

theorem stieltjes_measure_eq_derivative_density (f : StieltjesFunction ℝ)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval f a b) :
    f.measure = volume.withDensity (fun x => ENNReal.ofReal (deriv f x)) := by
  apply Measure.ext_of_Ioc
  intro a b hab
  have hac := hAC a b
  rw [StieltjesFunction.measure_Ioc, withDensity_apply _ measurableSet_Ioc,
    ←ofReal_integral_eq_lintegral_ofReal hac.intervalIntegrable_deriv.1
      (Filter.Eventually.of_forall (fun x => f.mono.deriv_nonneg)),
    ←intervalIntegral.integral_of_le hab.le, hac.integral_deriv_eq_sub]

end QuantitativeFollowup
