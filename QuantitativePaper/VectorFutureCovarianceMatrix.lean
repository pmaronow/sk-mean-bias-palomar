module
public import QuantitativePaper.VectorFutureCovarianceIntegral
public import QuantitativePaper.VectorMeasureMatrixOrder
public import FourPapersCommon.MatrixEntryPolarization
public import FourPapersCommon.ConditionalPolarization

@[expose] public section

/-! Literal coordinate matrices of the actual arbitrary-profile covariance
integral, with a common null set and the genuine future conditional law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureExpectedFutureCovarianceMatrix (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (q : Paper.Overlap) (ht : t ≤ 1) (u : Paper.Overlap) (p : VectorDisorderBrownianSample n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (vectorMeasureExpectedFutureCovariance μ β t a q ht u
      (EuclideanSpace.single i 1+EuclideanSpace.single j 1) p -
    vectorMeasureExpectedFutureCovariance μ β t a q ht u (EuclideanSpace.single i 1) p -
    vectorMeasureExpectedFutureCovariance μ β t a q ht u (EuclideanSpace.single j 1) p)/2

theorem vectorMeasureSpinCovariance_entry_polarization (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (i j : Fin n) :
    ∀ᵐp ∂vectorMeasureDisorderTilt μ β t a,
      vectorMeasureSpinCovariance μ β t a ht q p i j =
        (vectorMeasureConditionalVariance μ β t a ht q
            (EuclideanSpace.single i 1+EuclideanSpace.single j 1) p -
          vectorMeasureConditionalVariance μ β t a ht q (EuclideanSpace.single i 1) p -
          vectorMeasureConditionalVariance μ β t a ht q (EuclideanSpace.single j 1) p)/2 := by
  filter_upwards [vectorMeasureConditionalVariance_eq_covarianceQuadratic μ β t a ht q
    (EuclideanSpace.single i 1+EuclideanSpace.single j 1),
    vectorMeasureConditionalVariance_eq_covarianceQuadratic μ β t a ht q (EuclideanSpace.single i 1),
    vectorMeasureConditionalVariance_eq_covarianceQuadratic μ β t a ht q (EuclideanSpace.single j 1)] with p hp hi hj
  rw [hp, hi, hj]
  exact euclideanMatrixQuadratic_entry (vectorMeasureSpinCovariance μ β t a ht q p)
    (vectorMeasureSpinCovariance_symmetric μ β t a ht q p) i j

theorem vectorMeasureExpectedFutureCovarianceMatrix_condExp (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q u : Paper.Overlap) (ht : t ≤ 1) (hqu : q ≤ u) (i j : Fin n) :
    (vectorMeasureDisorderTilt μ β t a)[
      (fun p => vectorMeasureSpinCovariance μ β t a ht u p i j) |
      vectorBrownianFiltration n (q:ℝ).toNNReal] =ᵐ[vectorMeasureDisorderTilt μ β t a]
      fun p => vectorMeasureExpectedFutureCovarianceMatrix μ β t a q ht u p i j := by
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  let f := vectorMeasureConditionalVariance μ β t a ht u
    (EuclideanSpace.single i 1+EuclideanSpace.single j 1)
  let g := vectorMeasureConditionalVariance μ β t a ht u (EuclideanSpace.single i 1)
  let h := vectorMeasureConditionalVariance μ β t a ht u (EuclideanSpace.single j 1)
  have he := condExp_congr_ae (μ:=P) (m:=vectorBrownianFiltration n (q:ℝ).toNNReal)
    (vectorMeasureSpinCovariance_entry_polarization μ β t a ht u i j)
  have hl := condExp_polarization P (vectorBrownianFiltration n (q:ℝ).toNNReal) f g h
    (integrable_vectorMeasureConditionalVariance μ β t a ht u _)
    (integrable_vectorMeasureConditionalVariance μ β t a ht u _)
    (integrable_vectorMeasureConditionalVariance μ β t a ht u _)
  have hf := vectorMeasureExpectedFutureCovariance_condExp μ β t a q u ht hqu
    (EuclideanSpace.single i 1+EuclideanSpace.single j 1)
  have hg := vectorMeasureExpectedFutureCovariance_condExp μ β t a q u ht hqu (EuclideanSpace.single i 1)
  have hh := vectorMeasureExpectedFutureCovariance_condExp μ β t a q u ht hqu (EuclideanSpace.single j 1)
  filter_upwards [he, hl, hf, hg, hh] with p hep hlp hfp hgp hhp
  change _ = (vectorMeasureExpectedFutureCovariance μ β t a q ht u
    (EuclideanSpace.single i 1+EuclideanSpace.single j 1) p -
    vectorMeasureExpectedFutureCovariance μ β t a q ht u (EuclideanSpace.single i 1) p -
    vectorMeasureExpectedFutureCovariance μ β t a q ht u (EuclideanSpace.single j 1) p)/2
  dsimp only [f, g, h, P] at hlp
  rw [hep, hlp, hfp, hgp, hhp]

theorem integrable_vectorMeasureExpectedFutureCovariance_tail (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q : Paper.Overlap) (ht : t ≤ 1) (w : Field n)
    (p : VectorDisorderBrownianSample n) :
    Integrable (fun u : Paper.Overlap => if q < u then vectorMeasureExpectedFutureCovariance μ β t a q ht u w p else 0)
      (μ:Measure Paper.Overlap) := by
  have hm : Measurable (fun u : Paper.Overlap => vectorPastMeanSquareKernel μ β t a q ht u w p) :=
    (measurable_uncurry_vectorPastMeanSquareKernel μ β t a q ht w).comp
      (measurable_id.prodMk measurable_const)
  have hi : Integrable (fun u : Paper.Overlap => vectorPastMeanSquareKernel μ β t a q ht u w p)
      (μ:Measure Paper.Overlap) :=
    (integrable_const ((vectorDirectionBound w)^2)).mono' hm.aestronglyMeasurable
      (.of_forall fun u => norm_vectorPastMeanSquareKernel_le μ β t a q ht u w p)
  have hS : MeasurableSet {u : Paper.Overlap | q < u} := measurableSet_lt measurable_const measurable_id
  have hc := ((integrable_const (((vectorMeasureDisorderTilt μ β t a)[
    vectorMeasureTerminalSecondMoment μ β t ht w | vectorBrownianFiltration n (q:ℝ).toNNReal]) p)).sub hi).indicator hS
  apply hc.congr
  exact .of_forall fun u => by
    by_cases hqu : q < u <;> simp [vectorMeasureExpectedFutureCovariance, hqu, Pi.sub_apply]

theorem vectorMeasureHessianMatrix_future_covariance_integral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap) :
    ∀ᵐp ∂vectorMeasureDisorderTilt (n:=n) μ β t a, ∀i j : Fin n,
      vectorMeasureHessianMatrix μ β t ht.le q p i j =
        Paper.parisiCDF μ q*vectorMeasureSpinCovariance μ β t a ht.le q p i j +
        ∫u : Paper.Overlap, if q < u then vectorMeasureExpectedFutureCovarianceMatrix μ β t a q ht.le u p i j else 0
          ∂(μ:Measure Paper.Overlap) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  let w : Field n := EuclideanSpace.single i 1+EuclideanSpace.single j 1
  let v : Field n := EuclideanSpace.single i 1
  let z : Field n := EuclideanSpace.single j 1
  filter_upwards [vectorMeasureHessian_future_covariance_integral μ β t a hβ ht q w,
    vectorMeasureHessian_future_covariance_integral μ β t a hβ ht q v,
    vectorMeasureHessian_future_covariance_integral μ β t a hβ ht q z,
    vectorMeasureSpinCovariance_entry_polarization μ β t a ht.le q i j] with p hw hv hz hc
  have hH := euclideanMatrixQuadratic_entry (vectorMeasureHessianMatrix μ β t ht.le q p)
    (vectorMeasureHessianMatrix_symmetric μ β t ht.le q p) i j
  have hQ (b : Field n) : euclideanMatrixQuadratic (vectorMeasureHessianMatrix μ β t ht.le q p) b =
      vectorMeasureHessianQuadratic μ β t ht.le q b p :=
    (vectorMeasureHessianMatrix_quadratic μ β t ht.le q p b).symm
  rw [hQ, hQ, hQ] at hH
  change _ = (vectorMeasureHessianQuadratic μ β t ht.le q w p -
    vectorMeasureHessianQuadratic μ β t ht.le q v p-vectorMeasureHessianQuadratic μ β t ht.le q z p)/2 at hH
  let E := fun b : Field n => fun u : Paper.Overlap =>
    if q < u then vectorMeasureExpectedFutureCovariance μ β t a q ht.le u b p else 0
  have hi b : Integrable (E b) (μ:Measure Paper.Overlap) :=
    integrable_vectorMeasureExpectedFutureCovariance_tail μ β t a q ht.le b p
  have he : (fun u : Paper.Overlap => if q < u then vectorMeasureExpectedFutureCovarianceMatrix μ β t a q ht.le u p i j else 0) =
      fun u => (E w u-E v u-E z u)/2 := by
    funext u
    by_cases hqu : q < u <;> simp [vectorMeasureExpectedFutureCovarianceMatrix, E, w, v, z, hqu]
  rw [he, integral_div]
  have hInt : (∫u, E w u-E v u-E z u ∂(μ:Measure Paper.Overlap)) =
      (∫u, E w u ∂(μ:Measure Paper.Overlap)) - (∫u, E v u ∂(μ:Measure Paper.Overlap)) -
        ∫u, E z u ∂(μ:Measure Paper.Overlap) := by
    change (∫u, (E w-E v) u-E z u ∂(μ:Measure Paper.Overlap)) = _
    rw [integral_sub ((hi w).sub (hi v)) (hi z)]
    simp only [Pi.sub_apply]
    rw [integral_sub (hi w) (hi v)]
  rw [hInt]
  rw [hH, hc]
  change _ = Paper.parisiCDF μ q*((vectorMeasureConditionalVariance μ β t a ht.le q w p-
    vectorMeasureConditionalVariance μ β t a ht.le q v p-vectorMeasureConditionalVariance μ β t a ht.le q z p)/2) + _
  change _ = _ + ∫u, E w u ∂(μ:Measure Paper.Overlap) at hw
  change _ = _ + ∫u, E v u ∂(μ:Measure Paper.Overlap) at hv
  change _ = _ + ∫u, E z u ∂(μ:Measure Paper.Overlap) at hz
  linarith

end QuantitativePaper
