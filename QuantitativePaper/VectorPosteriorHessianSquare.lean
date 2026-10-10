module
public import QuantitativePaper.VectorIntegratedCovariance
public import QuantitativePaper.VectorTraceOrder
public import QuantitativePaper.VectorDyadicFixedHessianEnergy

@[expose] public section

/-! The proved finite posterior Brascamp--Lieb estimate expressed with the
actual Hilbert square of its field Hessian.  The positive root floor gives
every feature a positive denominator. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorFieldHessianMatrix_trace_square (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) :
    Matrix.trace (vectorFieldHessianMatrix s β t i x*vectorFieldHessianMatrix s β t i x)=
      vectorHessianHilbertSquare (vectorFieldHessian s β t x.1 (k+2-i) x.2) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  simp_rw [vectorFieldHessianMatrix_symmetric s β t i x,←pow_two]
  unfold vectorHessianHilbertSquare
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_comm]
  rfl

theorem continuous_vectorFieldHessianHilbertSquare (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) : Continuous (fun x : VectorState n=>
      vectorHessianHilbertSquare (vectorFieldHessian s β t x.1 (k+2-i) x.2)) := by
  unfold vectorHessianHilbertSquare
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact continuous_finset_sum _ fun j _=>continuous_finset_sum _ fun l _=>
    (continuous_vectorFieldHessian_component s β t (k+2-i) j l).pow 2

theorem vectorFeatureMass_floor (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1)
    (i : vectorPosteriorFeatureIndex k) :
    a≤observableDepthMass s (k+2-vectorPosteriorFeatureTime i) := by
  have hi : vectorPosteriorFeatureTime i≤k+1 := by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega
  have hi0 : 1≤vectorPosteriorFeatureTime i := by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega
  have he : k+2-(k+2-vectorPosteriorFeatureTime i)=vectorPosteriorFeatureTime i := by omega
  unfold observableDepthMass
  rw [ite_eq_right (by omega),he]
  exact ha.trans (s.m_mono' (vectorPosteriorFeatureTime i) hi 1 hi0)

theorem vectorFieldHessian_covariance_trace_le_square (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) (hm : 0<observableDepthMass s (k+2-i)) :
    Matrix.trace (vectorFieldHessianMatrix s β t i x*vectorSpinCovariance s β t i x)≤
      vectorHessianHilbertSquare (vectorFieldHessian s β t x.1 (k+2-i) x.2)/
        observableDepthMass s (k+2-i) := by
  apply (le_div_iff₀ hm).mpr
  rw [mul_comm,←vectorFieldHessianMatrix_trace_square]
  exact (vector_trace_covariance_order s β t i x).2.1

theorem integral_vector_covariance_trace_le_square (s : RSBScheme k) (β t a : ℝ)
    (i : ℕ) (hm : 0<observableDepthMass s (k+2-i)) :
    (∫p : VectorGaussianSpace n k×Configuration n,
      Matrix.trace (vectorFieldHessianMatrix s β t i (vectorEuclideanStateLinear s β t i p.1)*
        vectorSpinCovariance s β t i (vectorEuclideanStateLinear s β t i p.1))
      ∂vectorEuclideanJointLaw s β t a)≤
    (∫p : VectorGaussianSpace n k×Configuration n,
      vectorHessianHilbertSquare (vectorFieldHessian s β t
        (vectorEuclideanStateLinear s β t i p.1).1 (k+2-i)
        (vectorEuclideanStateLinear s β t i p.1).2)
      ∂vectorEuclideanJointLaw s β t a)/observableDepthMass s (k+2-i) := by
  let X:=fun p : VectorGaussianSpace n k×Configuration n=>vectorEuclideanStateLinear s β t i p.1
  have hX : Measurable X := by dsimp [X];fun_prop
  have hS : Integrable (fun p=>vectorHessianHilbertSquare
      (vectorFieldHessian s β t (X p).1 (k+2-i) (X p).2))
      (vectorEuclideanJointLaw s β t a) := by
    apply integrable_vectorEuclidean_bounded s β t a _
      ((continuous_vectorFieldHessianHilbertSquare s β t i).measurable.comp hX) ((n : ℝ)^3)
    intro p
    dsimp only [Function.comp_apply]
    rw [abs_of_nonneg (vectorHessianHilbertSquare_nonneg _)]
    exact vectorHessianHilbertSquare_le (norm_vectorFieldHessian_le s β t _ _ _)
  have hC : Measurable (fun p=>Matrix.trace
      (vectorFieldHessianMatrix s β t i (X p)*vectorSpinCovariance s β t i (X p))) := by
    simp_rw [matrix_trace_mul_vectorSpinCovariance]
    exact Finset.measurable_sum _ fun l _=>Finset.measurable_sum _ fun j _=>
      ((continuous_vectorFieldHessian_component s β t (k+2-i) j l).measurable.comp hX).mul
        ((measurable_vectorSpinCovariance_component s β t i l j).comp hX)
  have hCi : Integrable (fun p=>Matrix.trace
      (vectorFieldHessianMatrix s β t i (X p)*vectorSpinCovariance s β t i (X p)))
      (vectorEuclideanJointLaw s β t a) := by
    apply integrable_vectorEuclidean_bounded s β t a _ hC ((n : ℝ)^3/observableDepthMass s (k+2-i))
    intro p
    rw [abs_of_nonneg (vector_trace_covariance_order s β t i (X p)).1]
    exact (vectorFieldHessian_covariance_trace_le_square s β t i (X p) hm).trans
      (div_le_div_of_nonneg_right (vectorHessianHilbertSquare_le
        (norm_vectorFieldHessian_le s β t _ _ _)) hm.le)
  rw [←integral_div]
  exact integral_mono hCi (hS.div_const _) fun p=>
    vectorFieldHessian_covariance_trace_le_square s β t i (X p) hm

theorem vectorJoint_weightedOverlap_variance_le_hessian_square (hn : 0<n)
    (s : RSBScheme k) (β t a : ℝ) (hβ : β≠0) (ht : t<1) (hq : s.q 1=0)
    (ha0 : 0<a) (ha : a ≤ s.m 1) (kernel : ℝ→ℝ) :
    variance (fun p : VectorGaussianSpace n k×Configuration n=>
      vectorEuclideanWeightedOverlapScore s β t a kernel p.2 p.1) (vectorEuclideanJointLaw s β t a)≤
      (∑i,vectorPosteriorFeatureWeight s a i*(vectorPosteriorFeatureKernel s kernel i)^2*
        ((∫p : VectorGaussianSpace n k×Configuration n,
          vectorHessianHilbertSquare (vectorFieldHessian s β t
            (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) p.1).1
            (k+2-vectorPosteriorFeatureTime i)
            (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) p.1).2)
          ∂vectorEuclideanJointLaw s β t a)/
            observableDepthMass s (k+2-vectorPosteriorFeatureTime i)))/(n : ℝ)^2 := by
  apply (vectorJoint_weightedOverlap_variance_le_integrated_covariance hn s β t a hβ ht hq ha kernel).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left
    (integral_vector_covariance_trace_le_square s β t a (vectorPosteriorFeatureTime i)
      (ha0.trans_le (vectorFeatureMass_floor s a ha i)))
    (mul_nonneg (vectorPosteriorFeatureWeight_nonneg s a ha i) (sq_nonneg _))

end QuantitativePaper
