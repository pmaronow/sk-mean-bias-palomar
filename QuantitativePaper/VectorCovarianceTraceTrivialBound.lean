module
public import QuantitativePaper.VectorSupportCovarianceSquare
public import FourPapersCommon.PositiveMatrixTraceSquare

@[expose] public section

/-! The sharp elementary covariance-square trace bound for the actual
arbitrary-profile spin process. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasureSpinCovariance_trace_square_le_dimension
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ β t a,
      Matrix.trace (vectorMeasureSpinCovariance μ β t a ht.le q sample*
        vectorMeasureSpinCovariance μ β t a ht.le q sample)≤(n:ℝ)^2 := by
  filter_upwards [vectorMeasure_matrix_order μ β t a hβ ht q] with sample hs
  have hC:=hs.1
  have hnon : 0≤Matrix.trace (vectorMeasureSpinCovariance μ β t a ht.le q sample):=hC.trace_nonneg
  have htrace : Matrix.trace (vectorMeasureSpinCovariance μ β t a ht.le q sample)≤(n:ℝ):=by
    rw [vectorMeasureSpinCovariance_trace]
    exact sub_le_self _ (sq_nonneg _)
  exact (positive_matrix_trace_square_le _ hC).trans
    (pow_le_pow_left₀ hnon htrace 2)

theorem integral_vectorMeasureSpinCovariance_trace_square_le_dimension
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    (∫sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t a ht.le q sample*
        vectorMeasureSpinCovariance μ β t a ht.le q sample)
      ∂vectorMeasureDisorderTilt μ β t a)≤(n:ℝ)^2 := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  have h:=integral_mono_ae (integrable_vectorMeasureSpinCovariance_trace_square μ β t a ht.le q)
    (integrable_const ((n:ℝ)^2))
    (vectorMeasureSpinCovariance_trace_square_le_dimension μ β t a hβ ht q)
  simpa only [integral_const,probReal_univ,one_smul] using h

end QuantitativePaper
