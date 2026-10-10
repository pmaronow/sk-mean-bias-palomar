module
public import QuantitativePaper.VectorMeasurePhysicalConditionalVariance
public import QuantitativePaper.VectorCovarianceQuadratic
public import FourPapersCommon.ConditionalFiniteQuadratic

@[expose] public section

/-! A literal matrix of conditional terminal-spin covariances under the
actual arbitrary-profile law. Its quadratic form agrees with the genuine
directional conditional variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureSpinCovariance (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>(vectorMeasureDisorderTilt μ β t a)[
    vectorMeasureTerminalObservable μ β t ht (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))|
      vectorBrownianFiltration n (q : ℝ).toNNReal] sample-
    vectorMeasureSpinMean μ β t ht q sample i*vectorMeasureSpinMean μ β t ht q sample j

def vectorMeasureCovarianceQuadratic (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (w : Field n) : ℝ :=
  ∑i : Fin n,∑j : Fin n,vectorMeasureSpinCovariance μ β t a ht q sample i j*w i*w j

theorem vectorMeasureSpinCovariance_symmetric (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (i j : Fin n) :
    vectorMeasureSpinCovariance μ β t a ht q sample i j=
      vectorMeasureSpinCovariance μ β t a ht q sample j i := by
  have he : (fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ j))=
      fun σ=>Paper.spinSign (σ j)*Paper.spinSign (σ i) := by funext σ;ring
  unfold vectorMeasureSpinCovariance
  rw [he,mul_comm (vectorMeasureSpinMean μ β t ht q sample i)]

theorem vectorMeasureConditionalVariance_eq_covarianceQuadratic (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (w : Field n) :
    vectorMeasureConditionalVariance μ β t a ht q w=ᵐ[vectorMeasureDisorderTilt μ β t a]
      fun sample=>vectorMeasureCovarianceQuadratic μ β t a ht q sample w := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n):=inferInstance
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  let m:=vectorBrownianFiltration n (q : ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n):=ambient
  let T:=fun i j : Fin n=>vectorMeasureTerminalObservable μ β t ht
    (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))
  have hT (i j : Fin n) : Integrable (T i j) P:=integrable_vectorMeasureTerminalObservable μ β t a ht _
  have he : vectorMeasureTerminalSecondMoment μ β t ht w=
      fun sample=>∑i : Fin n,∑j : Fin n,(w i*w j)*T i j sample := by
    funext sample
    unfold vectorMeasureTerminalSecondMoment
    rw [funext (fieldDot_sq_eq_double_sum w)]
    simp_rw [terminalMean_sum,terminalMean_const_mul]
    rfl
  have hc:=condExp_double_sum_coeff P m T (fun i=>w i) hT
  filter_upwards [hc] with sample hs
  change P[vectorMeasureTerminalSecondMoment μ β t ht w|m] sample-
    (vectorMeasureMeanInDirection μ β t ht q w sample)^2=
      vectorMeasureCovarianceQuadratic μ β t a ht q sample w
  rw [he,hs]
  unfold vectorMeasureMeanInDirection
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    _=∑i : Fin n,∑j : Fin n,((w i*w j)*P[T i j|m] sample-
      (w i*vectorMeasureSpinMean μ β t ht q sample i)*
      (w j*vectorMeasureSpinMean μ β t ht q sample j)) := by
      simp only [Finset.sum_sub_distrib]
    _=_ := by
      unfold vectorMeasureCovarianceQuadratic
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold vectorMeasureSpinCovariance
      change (w i*w j)*P[T i j|m] sample-_=(_)*w i*w j
      ring

theorem condVar_vectorMeasure_terminal_direction_eq_matrix (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (w : Field n) :
    condVar (vectorSpinPast n (q : ℝ).toNNReal)
      (fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2)
      (vectorMeasureSpinPathLaw μ β t a ht.le)=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun p=>vectorMeasureCovarianceQuadratic μ β t a ht.le q p.1 w :=
  (condVar_vectorMeasure_terminal_direction μ β t a hβ ht q w).trans
    ((measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).quasiMeasurePreserving.ae
      (vectorMeasureConditionalVariance_eq_covarianceQuadratic μ β t a ht.le q w))

end QuantitativePaper
