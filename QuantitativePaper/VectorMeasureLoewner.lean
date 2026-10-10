module
public import QuantitativePaper.VectorMeasureCovarianceMatrix
public import FourPapersCommon.AEContinuousOrder

@[expose] public section

/-! A single common null set for the genuine arbitrary-profile matrix
covariance comparison, in every field direction simultaneously. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem continuous_vectorMeasureCovarianceQuadratic (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    Continuous (vectorMeasureCovarianceQuadratic μ β t a ht q sample) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((EuclideanSpace.proj i).continuous.const_mul _).mul (EuclideanSpace.proj j).continuous

theorem continuous_vectorMeasureHessianQuadratic_direction (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun w : Field n=>vectorMeasureHessianQuadratic μ β t ht q w sample) := by
  exact continuous_id.inner
    (vectorMeasureHessian μ β t q sample.1 (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample)).continuous

theorem vectorMeasureHessian_covariance_all_directions (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt μ β t a,∀w : Field n,
      Paper.parisiCDF μ q*vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w≤
        vectorMeasureHessianQuadratic μ β t ht.le q w sample ∧
      vectorMeasureHessianQuadratic μ β t ht.le q w sample≤
        vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w := by
  have hper (w : Field n) : ∀ᵐsample ∂vectorMeasureDisorderTilt μ β t a,
      Paper.parisiCDF μ q*vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w≤
        vectorMeasureHessianQuadratic μ β t ht.le q w sample ∧
      vectorMeasureHessianQuadratic μ β t ht.le q w sample≤
        vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w := by
    filter_upwards [vectorMeasureHessian_conditionalVariance_bounds μ β t a hβ ht q w,
      vectorMeasureConditionalVariance_eq_covarianceQuadratic μ β t a ht.le q w] with sample hs he
    rwa [he] at hs
  have hleft:=ae_all_continuous_le (vectorMeasureDisorderTilt μ β t a)
    (fun sample w=>Paper.parisiCDF μ q*vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w)
    (fun sample w=>vectorMeasureHessianQuadratic μ β t ht.le q w sample)
    (fun sample=>(continuous_vectorMeasureCovarianceQuadratic μ β t a ht.le q sample).const_mul _)
    (continuous_vectorMeasureHessianQuadratic_direction μ β t ht.le q)
    (fun w=>(hper w).mono fun _ hs=>hs.1)
  have hright:=ae_all_continuous_le (vectorMeasureDisorderTilt μ β t a)
    (fun sample w=>vectorMeasureHessianQuadratic μ β t ht.le q w sample)
    (fun sample w=>vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w)
    (continuous_vectorMeasureHessianQuadratic_direction μ β t ht.le q)
    (continuous_vectorMeasureCovarianceQuadratic μ β t a ht.le q)
    (fun w=>(hper w).mono fun _ hs=>hs.2)
  filter_upwards [hleft,hright] with sample hl hr
  exact fun w=>⟨hl w,hr w⟩

theorem vectorMeasureCovarianceQuadratic_nonneg (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt μ β t a,∀w : Field n,
      0≤vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w := by
  filter_upwards [vectorMeasureHessian_covariance_all_directions μ β t a hβ ht q] with sample hs
  exact fun w=>(vectorMeasureHessianQuadratic_nonneg μ β t ht.le q w sample).trans (hs w).2

theorem vectorMeasureHessian_physical_covariance_all_directions (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    ∀ᵐp ∂vectorMeasureSpinPathLaw μ β t a ht.le,∀w : Field n,
      Paper.parisiCDF μ q*vectorMeasureCovarianceQuadratic μ β t a ht.le q p.1 w≤
        vectorMeasureHessianQuadratic μ β t ht.le q w p.1 ∧
      vectorMeasureHessianQuadratic μ β t ht.le q w p.1≤
        vectorMeasureCovarianceQuadratic μ β t a ht.le q p.1 w :=
  (measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).quasiMeasurePreserving.ae
    (vectorMeasureHessian_covariance_all_directions μ β t a hβ ht q)

end QuantitativePaper
