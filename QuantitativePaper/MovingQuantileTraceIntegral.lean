module
public import FourPapersCommon.QuantileTraceCutoffIntegral
public import QuantitativePaper.VectorCovarianceTraceTrivialBound
public import QuantitativePaper.VectorCovarianceTraceMeasurability
public import QuantitativeFollowup.ParisiFreeQuantileSupport

@[expose] public section

/-! The actual covariance trace integral at a moving free-quantile cutoff. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativeFollowup
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_moving_quantile_trace_integral (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor s)
    (hmin : ∀ ν ∈ scalarFloor s, vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s)
    (u : ℝ) (hu : u ∈ Icc s 1) :
    (∫ v in Ioo (0 : ℝ) (1-s),
      (∫ sample : VectorDisorderBrownianSample n,
        Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le (parisiFreeQuantile μ s v) sample *
          vectorMeasureSpinCovariance μ β t s ht.le (parisiFreeQuantile μ s v) sample)
        ∂vectorMeasureDisorderTilt μ β t s)/(n : ℝ)^2) ≤
      (u-s)+1/(((n : ℝ)*((1-t)*β^2))*u) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < (1-t)*β^2 := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  let T : Paper.Overlap → ℝ := fun q => ∫ sample : VectorDisorderBrownianSample n,
    Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample *
      vectorMeasureSpinCovariance μ β t s ht.le q sample) ∂vectorMeasureDisorderTilt μ β t s
  let ψ : ℝ → ℝ := fun v => T (parisiFreeQuantile μ s v)/(n : ℝ)^2
  have hT : Measurable T := measurable_integral_vectorMeasureSpinCovariance_trace_square μ β t s ht.le
  have hψ : Measurable ψ := (hT.comp (parisiFreeQuantile_measurable μ s)).div_const _
  have hb : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1 := by
    intro v
    have hlo : 0 ≤ T (parisiFreeQuantile μ s v) := by
      apply integral_nonneg
      intro sample
      change 0 ≤ Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le (parisiFreeQuantile μ s v) sample *
        vectorMeasureSpinCovariance μ β t s ht.le (parisiFreeQuantile μ s v) sample)
      rw [symmetric_matrix_square_trace _ (vectorMeasureSpinCovariance_symmetric μ β t s ht.le
        (parisiFreeQuantile μ s v) sample)]
      positivity
    have hhi := integral_vectorMeasureSpinCovariance_trace_square_le_dimension (n := n) μ β t s hβ ht
      (parisiFreeQuantile μ s v)
    exact ⟨div_nonneg hlo (sq_nonneg _), (div_le_one (sq_pos_of_pos hn0)).mpr hhi⟩
  have htail : ∀ v ∈ Ioo (0 : ℝ) (1-s), ψ v ≤ 1/(((n : ℝ)*((1-t)*β^2))*(s+v)^2) := by
    intro v hv
    have hq := parisiFreeQuantile_mem_support μ s ⟨hs.1.le, hs.2.le⟩ (Ioo_subset_Ioc_self hv)
    have hbd := vector_free_support_trace_covariance_square_bound hn μ s hs hμ β t hβ ht hmin _ hq
    have hmass := parisiCDF_freeQuantile_lower μ s ⟨hs.1.le, hs.2.le⟩ (Ioo_subset_Ioc_self hv)
    have hsv : 0 < s+v := by linarith [hs.1, hv.1]
    have hm : 0 < Paper.parisiCDF μ (parisiFreeQuantile μ s v) := hsv.trans_le hmass
    have he : ((n : ℝ)/(((1-t)*β^2)*(Paper.parisiCDF μ (parisiFreeQuantile μ s v))^2))/(n : ℝ)^2 =
        1/(((n : ℝ)*((1-t)*β^2))*(Paper.parisiCDF μ (parisiFreeQuantile μ s v))^2) := by
      field_simp
    apply (div_le_div_of_nonneg_right hbd (sq_nonneg (n : ℝ))).trans
    rw [he]
    apply one_div_le_one_div_of_le
      (mul_pos (mul_pos hn0 hc) (sq_pos_of_pos hsv))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsv.le hmass 2) (mul_pos hn0 hc).le
  exact bounded_quantile_trace_cutoff_integral ψ hψ hb ((n : ℝ)*((1-t)*β^2)) s u
    (mul_pos hn0 hc) hs hu htail

end QuantitativePaper
