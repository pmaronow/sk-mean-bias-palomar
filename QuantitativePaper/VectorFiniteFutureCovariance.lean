module
public import QuantitativePaper.VectorFutureCovarianceKernels

@[expose] public section

/-! The exact finite-profile future-covariance identity. Its future terms
are genuine expectations under the constructed normalized Gaussian kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem vectorFutureCovarianceKernelSum_eq_correction {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (b : Configuration n → ℝ) (R : ℝ≥0) (hb : ∀σ, |b σ| ≤ R)
    (j : ℕ) (x : VectorState n) :
    vectorFutureCovarianceKernelSum s β t b j x =
      vectorFutureCovarianceCorrection s β t x.1 b j 0 x.2 := by
  induction j generalizing x with
  | zero => simp [vectorFutureCovarianceKernelSum, vectorFutureCovarianceCorrection]
  | succ j ih =>
    rw [vectorFutureCovarianceKernelSum_step s β t b R hb j]
    let F := fun y : VectorState n =>
      (observableDepthMass s j - observableDepthMass s (j+1))*vectorDepthCovariance s β t b j y +
        vectorFutureCovarianceKernelSum s β t b j y
    have hF : Measurable F :=
      ((measurable_vectorDepthCovariance s β t b j).const_mul _).add
        (measurable_vectorFutureCovarianceKernelSum s β t b j)
    change (∫y, F y ∂vectorDepthKernel s β t j x) = _
    rw [vectorDepthKernel, integral_vectorStateKernel_response _ (measurable_vectorRecursion s β t j)
      (Real.sqrt (n:ℝ)).toNNReal (fun p => vectorRecursion_lipschitz s β t p j) F hF]
    simp only [vectorFutureCovarianceCorrection, vectorPerturbedRecursion_zero]
    congr 1
    funext z
    dsimp only [F, vectorDepthCovariance]
    rw [ih]

theorem vectorFieldHessian_future_covariance_sum {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x w : Field n) :
    inner ℝ w (vectorFieldHessian s β t p j x w) =
      observableDepthMass s j *
        vectorObservableCovariance s β t p (fun σ => fieldDot w σ) j 0 x +
          vectorFutureCovarianceKernelSum s β t (fun σ => fieldDot w σ) j (p,x) := by
  rw [vectorFutureCovarianceKernelSum_eq_correction s β t _
    ⟨Real.sqrt (n:ℝ)*‖w‖, mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)⟩
    (abs_fieldDot w)]
  exact vectorFieldHessian_future_covariance s β t p j x w

end QuantitativePaper
