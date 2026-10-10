module
public import QuantitativeFollowup.MeanCovarianceDyadic
public import QuantitativeFollowup.DyadicLogOptimization

@[expose] public section

/-! Follow-up Lemma 4.3 with its literal constant and logarithmic budget,
derived for the actual minimizing profile and physical mean/covariance. -/
noncomputable section
open MeasureTheory Set QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem vector_mean_covariance_residual_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (p q : Paper.Overlap) (hpq : p≤q)
    (hq : q∈(parisiFreeMeasure μ s).support) :
    vectorMeanCovarianceIncrement (n:=n) μ β t a ht.le p q≤
      56*(1+logPlus ((n:ℝ)*((1-t)*β^2)*((q:ℝ)-p)))^2/
        ((n:ℝ)*((1-t)*β^2)*(Paper.parisiCDF μ (dyadicOverlap p q hpq 1))^2) := by
  apply dyadic_residual_optimized_bound
  · exact mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  · exact hs.1.trans_le (scalarFloor_cdf_lower hμ (dyadicOverlap p q hpq 1).property.1)
  · exact Paper.parisiCDF_le_one μ _
  · exact sub_nonneg.mpr hpq
  · intro K _
    exact vector_mean_covariance_dyadic_bound hn μ s hs hμ β t a hβ ht ha hmin p q hpq hq K

theorem covariance_of_mean_increment (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (p q : Paper.Overlap) (hpq : p≤q)
    (hq : q∈(parisiFreeMeasure μ s).support) :
    (∀K : ℕ,1≤K→vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le p q≤
      (K+1:ℝ)*(4*K/((n:ℝ)*((1-t)*β^2)*(Paper.parisiCDF μ (dyadicOverlap p q hpq 1))^2)+
        2*((q:ℝ)-p)*(1/2:ℝ)^K)) ∧
    vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le p q≤
      56*(1+logPlus ((n:ℝ)*((1-t)*β^2)*((q:ℝ)-p)))^2/
        ((n:ℝ)*((1-t)*β^2)*(Paper.parisiCDF μ (dyadicOverlap p q hpq 1))^2) := by
  exact ⟨fun K _=>vector_mean_covariance_dyadic_bound hn μ s hs hμ β t s hβ ht hs.1.le hmin p q hpq hq K,
    vector_mean_covariance_residual_bound hn μ s hs hμ β t s hβ ht hs.1.le hmin p q hpq hq⟩

end QuantitativeFollowup
