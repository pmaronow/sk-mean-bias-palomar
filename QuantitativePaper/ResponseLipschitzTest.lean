module
public import QuantitativePaper.VectorProfileActualC1Source
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section

/-! Genuine Lipschitz tests, with their a.e. derivatives. Smoothness of
the derivative is not required by the response inequality. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace QuantitativePaper
structure ResponseLipschitzTest where
  value : ℝ→ℝ
  lipschitzBound : ℝ≥0
  lipschitz : LipschitzWith lipschitzBound value
  zero_left : value 0=0
  zero_right : value 1=0

namespace ResponseLipschitzTest

def slope (w : ResponseLipschitzTest) : ℝ→ℝ:=deriv w.value

theorem continuous (w : ResponseLipschitzTest) : Continuous w.value:=w.lipschitz.continuous

theorem measurable_slope (w : ResponseLipschitzTest) : Measurable w.slope:=measurable_deriv w.value

theorem slope_bound (w : ResponseLipschitzTest) (q : ℝ) : ‖w.slope q‖≤w.lipschitzBound:=
  norm_deriv_le_of_lipschitz w.lipschitz

theorem absolutelyContinuous (w : ResponseLipschitzTest) (a b : ℝ) :
    AbsolutelyContinuousOnInterval w.value a b:=w.lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval

end ResponseLipschitzTest

theorem intervalIntegrable_responseLipschitzSlope_mul (w : ResponseLipschitzTest) (a b : ℝ)
    (R : ℝ→ℝ) (hR : IntervalIntegrable R volume a b) :
    IntervalIntegrable (fun q=>w.slope q*R q) volume a b:=by
  constructor
  · exact hR.1.bdd_mul w.measurable_slope.aestronglyMeasurable (.of_forall w.slope_bound)
  · exact hR.2.bdd_mul w.measurable_slope.aestronglyMeasurable (.of_forall w.slope_bound)

theorem intervalIntegrable_responseLipschitz_tested (w : ResponseLipschitzTest) (a b : ℝ)
    (R H : ℝ→ℝ) (hR : ContinuousOn R (uIcc a b))
    (hH : IntervalIntegrable H volume a b) :
    IntervalIntegrable (fun q=>w.slope q*R q+w.value q*H q) volume a b:=
  (intervalIntegrable_responseLipschitzSlope_mul w a b R hR.intervalIntegrable).add
    (hH.continuousOn_mul w.continuous.continuousOn)

theorem intervalIntegrable_responseLipschitzSlope_sq_mul (w : ResponseLipschitzTest) (a b : ℝ)
    (R : ℝ→ℝ) (hR : IntervalIntegrable R volume a b) :
    IntervalIntegrable (fun q=>(w.slope q)^2*R q) volume a b:=by
  have hb (q : ℝ) : ‖(w.slope q)^2‖≤(w.lipschitzBound:ℝ)^2:=by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (w.slope_bound q) 2
  constructor
  · exact hR.1.bdd_mul (w.measurable_slope.pow_const 2).aestronglyMeasurable (.of_forall hb)
  · exact hR.2.bdd_mul (w.measurable_slope.pow_const 2).aestronglyMeasurable (.of_forall hb)

theorem intervalIntegrable_responseLipschitz_squared_tested (w : ResponseLipschitzTest) (a b : ℝ)
    (R H : ℝ→ℝ) (hR : ContinuousOn R (uIcc a b))
    (hH : IntervalIntegrable H volume a b) :
    IntervalIntegrable (fun q=>2*w.slope q*w.value q*R q+(w.value q)^2*H q) volume a b:=by
  have hi : IntervalIntegrable (fun q=>w.slope q*(w.value q*R q)) volume a b:=
    intervalIntegrable_responseLipschitzSlope_mul w a b _
      (hR.intervalIntegrable.continuousOn_mul w.continuous.continuousOn)
  have hh:=(hi.const_mul 2).add (hH.continuousOn_mul (w.continuous.pow 2).continuousOn)
  convert hh using 1
  funext q
  simp only [Pi.pow_apply]
  ring

end QuantitativePaper
