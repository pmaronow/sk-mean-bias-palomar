module
public import QuantitativePaper.ResponseTentTestedFTC

@[expose] public section

/-! Actual measurable bounded tent slopes and the required integrable
tested products on every finite interval. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem measurable_responseTentSlope (ell : ℝ) : Measurable (responseTentSlope ell):=by
  unfold responseTentSlope
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const))

theorem norm_responseTentSlope_le (ell q : ℝ) : ‖responseTentSlope ell q‖≤|4/ell|:=by
  unfold responseTentSlope
  split_ifs <;> simp only [Real.norm_eq_abs,abs_neg,abs_zero,le_refl,abs_nonneg]

theorem intervalIntegrable_responseTentSlope_mul (ell a b : ℝ) (R : ℝ→ℝ)
    (hR : IntervalIntegrable R volume a b) :
    IntervalIntegrable (fun q=>responseTentSlope ell q*R q) volume a b:=by
  rw [intervalIntegrable_iff] at hR ⊢
  exact hR.bdd_mul (measurable_responseTentSlope ell).aestronglyMeasurable
    (.of_forall fun q=>norm_responseTentSlope_le ell q)

theorem intervalIntegrable_responseTent_tested (ell a b : ℝ) (R H : ℝ→ℝ)
    (hR : ContinuousOn R (uIcc a b)) (hH : IntervalIntegrable H volume a b) :
    IntervalIntegrable (fun q=>responseTentSlope ell q*R q+responseTent ell q*H q) volume a b:=by
  exact (intervalIntegrable_responseTentSlope_mul ell a b R hR.intervalIntegrable).add
    (hH.continuousOn_mul (continuous_responseTent ell).continuousOn)

theorem intervalIntegrable_responseTent_squared_tested (ell a b : ℝ) (R H : ℝ→ℝ)
    (hR : ContinuousOn R (uIcc a b)) (hH : IntervalIntegrable H volume a b) :
    IntervalIntegrable (fun q=>2*responseTentSlope ell q*responseTent ell q*R q+
      (responseTent ell q)^2*H q) volume a b:=by
  have h₁:=intervalIntegrable_responseTentSlope_mul ell a b
    (fun q=>responseTent ell q*R q) ((continuous_responseTent ell).continuousOn.mul hR).intervalIntegrable
  have h₂:=hH.continuousOn_mul ((continuous_responseTent ell).pow 2).continuousOn
  have hh:=(h₁.const_mul 2).add h₂
  convert hh using 1
  funext q
  simp only [Pi.pow_apply]
  ring

end QuantitativePaper
