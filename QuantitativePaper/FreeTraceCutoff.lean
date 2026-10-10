module
public import QuantitativePaper.MovingQuantileTraceIntegral

@[expose] public section

/-! Transport of the actual covariance trace estimate to its literal free Stieltjes law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativeFollowup
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1600000
variable {n : ℕ}

theorem vector_free_trace_integral_eq_quantile (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t ≤ 1) :
    (∫ q, (∫ sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t s ht q sample *
        vectorMeasureSpinCovariance μ β t s ht q sample) ∂vectorMeasureDisorderTilt μ β t s)/(n : ℝ)^2
      ∂parisiFreeMeasure μ s) =
    ∫ v in Ioo (0 : ℝ) (1-s), (∫ sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t s ht (parisiFreeQuantile μ s v) sample *
        vectorMeasureSpinCovariance μ β t s ht (parisiFreeQuantile μ s v) sample)
      ∂vectorMeasureDisorderTilt μ β t s)/(n : ℝ)^2 := by
  rw [integral_parisiFreeMeasure μ s _
    ((measurable_integral_vectorMeasureSpinCovariance_trace_square μ β t s ht).div_const _),
    integral_Ioc_eq_integral_Ioo]

theorem vector_free_trace_cutoff (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor s)
    (hmin : ∀ ν ∈ scalarFloor s, vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s)
    (u : ℝ) (hu : u ∈ Icc s 1) :
    (∫ q, (∫ sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample *
        vectorMeasureSpinCovariance μ β t s ht.le q sample) ∂vectorMeasureDisorderTilt μ β t s)/(n : ℝ)^2
      ∂parisiFreeMeasure μ s) ≤ (u-s)+1/(((n : ℝ)*((1-t)*β^2))*u) := by
  rw [vector_free_trace_integral_eq_quantile μ s β t ht.le]
  exact vector_moving_quantile_trace_integral hn μ s β t hβ ht hs hμ hmin u hu

theorem vector_free_trace_floor_bound (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor s)
    (hmin : ∀ ν ∈ scalarFloor s, vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s) :
    (∫ q, (∫ sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample *
        vectorMeasureSpinCovariance μ β t s ht.le q sample) ∂vectorMeasureDisorderTilt μ β t s)/(n : ℝ)^2
      ∂parisiFreeMeasure μ s) ≤ 1/(((n : ℝ)*((1-t)*β^2))*s) := by
  simpa only [sub_self, zero_add] using
    vector_free_trace_cutoff hn μ s β t hβ ht hs hμ hmin s ⟨le_rfl, hs.2.le⟩

end QuantitativePaper
