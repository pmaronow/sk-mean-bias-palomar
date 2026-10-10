module
public import QuantitativePaper.VectorProfileActualC1Source

@[expose] public section

/-! Concrete C¹ tests vanishing at the physical endpoints, and their
genuine integrable product-rule sources. -/
noncomputable section
open MeasureTheory Set
namespace QuantitativePaper
structure ResponseC1Test where
  value : ℝ→ℝ
  slope : ℝ→ℝ
  continuous : Continuous value
  continuous_slope : Continuous slope
  hasDerivAt : ∀q,HasDerivAt value (slope q) q
  zero_left : value 0=0
  zero_right : value 1=0

theorem intervalIntegrable_responseC1_tested (w : ResponseC1Test) (a b : ℝ)
    (R H : ℝ→ℝ) (hR : ContinuousOn R (uIcc a b))
    (hH : IntervalIntegrable H volume a b) :
    IntervalIntegrable (fun q=>w.slope q*R q+w.value q*H q) volume a b:=by
  exact (hR.intervalIntegrable.continuousOn_mul w.continuous_slope.continuousOn).add
    (hH.continuousOn_mul w.continuous.continuousOn)

theorem intervalIntegrable_responseC1Slope_sq_mul (w : ResponseC1Test) (a b : ℝ)
    (R : ℝ→ℝ) (hR : IntervalIntegrable R volume a b) :
    IntervalIntegrable (fun q=>(w.slope q)^2*R q) volume a b:=
  hR.continuousOn_mul (w.continuous_slope.pow 2).continuousOn

theorem intervalIntegrable_responseC1_squared_tested (w : ResponseC1Test) (a b : ℝ)
    (R H : ℝ→ℝ) (hR : ContinuousOn R (uIcc a b))
    (hH : IntervalIntegrable H volume a b) :
    IntervalIntegrable (fun q=>2*w.slope q*w.value q*R q+(w.value q)^2*H q) volume a b:=by
  have hc : Continuous (fun q=>2*w.slope q*w.value q):=
    (continuous_const.mul w.continuous_slope).mul w.continuous
  exact (hR.intervalIntegrable.continuousOn_mul hc.continuousOn).add
    (hH.continuousOn_mul (w.continuous.pow 2).continuousOn)

end QuantitativePaper
