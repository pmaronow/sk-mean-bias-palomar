module
public import QuantitativeFollowup.SupportingSourceNormalization
public import QuantitativeFollowup.SmallIntervalDecomposition
public import QuantitativeFollowup.VectorCubicFreeMeasure
public import QuantitativeFollowup.VectorSupportContact

@[expose] public section

/-! Identification of the printed cavity observables with the actual
integrated thermal, covariance, variance and cubic quantities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem followupCavity_thermal_trace_integral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) :
    (∫q, foundationThermalTrace (n:=n) μ β t a ht q ∂parisiFreeMeasure μ a) =
      vectorInterpolationTraceError (n:=n) μ a β t ht := rfl

theorem followupCavity_source_covariance_integral (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) :
    followupSourceMeanCovarianceIntegral (n:=n) μ β t a ht.le =
      vectorMeanDirectionCovarianceIntegral (n:=n) μ a β t a ht.le := by
  unfold followupSourceMeanCovarianceIntegral vectorMeanDirectionCovarianceIntegral
  exact integral_congr_ae (.of_forall fun q =>
    smallInterval_mean_covariance_eq hn μ β t a hβ ht q)

theorem followupCavity_source_variance_integral (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1) :
    followupSourceMeanVarianceIntegral (n:=n) μ β t a ht =
      vectorIntegratedSelfOverlapVariance (n:=n) μ a β t ht :=
  (vectorIntegratedSelfOverlapVariance_eq_free_integral hn μ a β t ht).symm

theorem followupCavity_source_cubic_integral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) :
    followupSourceCubicIntegral (n:=n) μ β t a ht =
      vectorIntegratedSelfOverlapCubic (n:=n) μ a β t ht :=
  (vectorIntegratedSelfOverlapCubic_eq_free_integral μ a β t ht).symm

theorem followupCavity_minimizer_no_upper_atom (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (hmin : ∀ν ∈ scalarFloor a, vectorMeasureFunctional n μ β t a ≤
      vectorMeasureFunctional n ν β t a) :
    parisiFreeMeasure μ a {(1 : Paper.Overlap)} = 0 := by
  have hout : (1 : Paper.Overlap) ∉ (parisiFreeMeasure μ a).support := by
    intro hmem
    have h := (vector_free_support_contact hn μ a ⟨ha.1.le, ha.2⟩ hμ β t a hβ ht
      ha.1.le hmin 1 hmem).1
    norm_num at h
  apply Measure.measure_eq_zero_of_isCompact_subset_compl_support isCompact_singleton
  simpa only [singleton_subset_iff, mem_compl_iff] using hout

end QuantitativeFollowup
