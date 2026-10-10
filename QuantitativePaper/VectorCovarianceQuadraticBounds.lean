module
public import QuantitativePaper.VectorMeasureCovarianceTrace
public import QuantitativePaper.VectorDirectionCovarianceEvolution
public import FourPapersCommon.PositiveQuadraticBounds

@[expose] public section

/-! Sharp physical covariance bounds and the positive-quadratic-form
inequality for finite sums of square-integrable random vectors. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem vectorMeasureCovarianceQuadratic_le_dimension (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ β t a,∀w : Field n,
      vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w≤(n:ℝ)*‖w‖^2 := by
  filter_upwards [vectorMeasure_matrix_order μ β t a hβ ht q] with sample hs
  intro w
  have h := positive_matrix_quadratic_le_trace _ hs.1 w
  change vectorMeasureCovarianceQuadratic μ β t a ht.le q sample w≤_ at h
  exact h.trans (mul_le_mul_of_nonneg_right (by
    rw [vectorMeasureSpinCovariance_trace]
    exact sub_le_self _ (sq_nonneg _)) (sq_nonneg _))

theorem vectorDirectionCovariance_le_dimension_moment (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : MemLp b 2 (vectorMeasureDisorderTilt μ β t a)) :
    vectorDirectionCovariance μ β t a ht.le b q≤
      (n:ℝ)*(∫sample,‖b sample‖^2∂vectorMeasureDisorderTilt μ β t a) := by
  have hi := hb.norm.integrable_mul hb.norm
  change Integrable (fun sample=>‖b sample‖*‖b sample‖) _ at hi
  have hi' : Integrable (fun sample=>‖b sample‖^2) (vectorMeasureDisorderTilt μ β t a) := by
    simpa only [pow_two] using hi
  rw [←integral_const_mul]
  apply integral_mono_ae (integrable_vectorMeasureRandomCovariance μ β t a ht.le q b hb) (hi'.const_mul _)
  filter_upwards [vectorMeasureCovarianceQuadratic_le_dimension μ β t a hβ ht q] with sample hs
  exact hs (b sample)

theorem vectorDirectionCovariance_sum_le {J : Type*} [Fintype J]
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (b : J→VectorDisorderBrownianSample n→Field n)
    (hb : ∀j,MemLp (b j) 2 (vectorMeasureDisorderTilt μ β t a)) :
    vectorDirectionCovariance μ β t a ht.le (fun sample=>∑j : J,b j sample) q≤
      (Fintype.card J:ℝ)*∑j : J,vectorDirectionCovariance μ β t a ht.le (b j) q := by
  classical
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  have hsum : MemLp (fun sample=>∑j : J,b j sample) 2 P :=
    memLp_finsetSum Finset.univ (fun j _=>hb j)
  have hj (j : J) := integrable_vectorMeasureRandomCovariance μ β t a ht.le q (b j) (hb j)
  have he : (∫sample,(Fintype.card J:ℝ)*∑j : J,vectorMeasureCovarianceQuadratic μ β t a ht.le q sample (b j sample)∂P)=
      (Fintype.card J:ℝ)*∑j : J,vectorDirectionCovariance μ β t a ht.le (b j) q := by
    rw [integral_const_mul,integral_finsetSum _ (fun j _=>hj j)]
    rfl
  rw [←he]
  apply integral_mono_ae (integrable_vectorMeasureRandomCovariance μ β t a ht.le q _ hsum)
    ((integrable_finsetSum _ (fun j _=>hj j)).const_mul _)
  filter_upwards [vectorMeasure_matrix_order μ β t a hβ ht q] with sample hs
  exact positive_matrix_quadratic_sum_le _ hs.1 (fun j=>b j sample)

end QuantitativePaper
