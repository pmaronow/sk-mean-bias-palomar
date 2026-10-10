module
public import QuantitativeFollowup.QuantileWindowCovarianceSplit

@[expose] public section

/-! Actual expectation/window integrability and the uniform averaged
residual budget used in the mean-direction covariance estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter QuantitativePaper
open scoped NNReal ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integrable_quantileWindowMeanCovarianceIncrement (μ : Paper.ParisiMeasure)
    (s β t a v x : ℝ) (ht : t≤1) (hx : 0<x) (q : Paper.Overlap) :
    Integrable (fun w=>vectorMeanCovarianceIncrement (n:=n) μ β t a ht
      (parisiPaddedFreeQuantile μ s w) q) (quantileWindowAveraging v x) := by
  let :=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  exact (integrable_vectorQuantileResidualQuadratic (n:=n) μ s β t a v x ht hx q).integral_prod_left.div_const _

theorem vector_quantile_window_residual_average_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hv : v∈Ioc (0:ℝ) (1-s)) :
    (∫w,vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le
      (parisiPaddedFreeQuantile μ s w) (parisiFreeQuantile μ s v)
      ∂quantileWindowAveraging v ((s+v)/2))≤
        224*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*(s+v)^2) := by
  have hx : 0<(s+v)/2:=by linarith [hs.1,hv.1]
  let :=quantileWindowAveraging_probability v ((s+v)/2) hx
  have hi:=integrable_quantileWindowMeanCovarianceIncrement (n:=n) μ s β t s v ((s+v)/2) ht.le hx
    (parisiFreeQuantile μ s v)
  have ha : ∀ᵐw ∂quantileWindowAveraging v ((s+v)/2),w∈Ioc (v-(s+v)/2) v :=
    Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
  have h:=integral_mono_ae hi (integrable_const
    (224*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*(s+v)^2)))
    (ha.mono fun w hw=>vector_quantile_window_residual_bound hn μ s β t v hβ ht hs hμ hmin hv w hw)
  simpa only [integral_const,probReal_univ,one_smul] using h

end QuantitativeFollowup
