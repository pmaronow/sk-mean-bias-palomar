module
public import QuantitativePaper.VectorEnergyIntegration
public import QuantitativePaper.VectorCovarianceTrace

@[expose] public section

/-! The finite-profile integrated covariance bound, under the actual joint
disorder/field/spin law. Its conditional covariance is identified from the
proved terminal-spin conditional expectation, not supplied as a hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem integrable_vectorSpinHessianEnergy_joint {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (i : ℕ) :
    Integrable (fun p : VectorGaussianSpace n k × Configuration n =>
      vectorSpinHessianEnergy s β t (k+2-i) p.2 (vectorEuclideanStateLinear s β t i p.1))
      (vectorEuclideanJointLaw s β t a) := by
  obtain ⟨B,hB,hBound⟩ := exists_vectorSpinHessianEnergy_bound (n := n) s β t (k+2-i)
  apply integrable_vectorEuclidean_bounded s β t a _ ?_ B
    (fun p => hBound p.2 (vectorEuclideanStateLinear s β t i p.1))
  exact measurable_from_prod_countable_left fun σ =>
    ((continuous_vectorSpinHessianEnergy s β t (k+2-i) σ).comp
      (vectorEuclideanStateLinear s β t i).continuous).measurable

theorem integral_vectorWeightedHessianEnergy_eq_trace {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (kernel : ℝ → ℝ) :
    (∫p : VectorGaussianSpace n k × Configuration n,
      vectorWeightedHessianEnergy s β t a kernel p.2 p.1 ∂vectorEuclideanJointLaw s β t a)=
      (∑ i,vectorPosteriorFeatureWeight s a i*(vectorPosteriorFeatureKernel s kernel i)^2*
        ∫p : VectorGaussianSpace n k × Configuration n,
          Matrix.trace (vectorFieldHessianMatrix s β t (vectorPosteriorFeatureTime i)
              (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) p.1)*
            vectorSpinCovariance s β t (vectorPosteriorFeatureTime i)
              (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) p.1))
          ∂vectorEuclideanJointLaw s β t a)/(n : ℝ)^2 := by
  classical
  unfold vectorWeightedHessianEnergy
  rw [integral_div]
  congr 1
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_vectorSpinHessianEnergy_joint s β t a (vectorPosteriorFeatureTime i)).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  have hi : vectorPosteriorFeatureTime i ≤ k+2 := by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega
  rw [integral_const_mul,integral_vectorSpinHessianEnergy_eq_trace (n := n) s β t a
    (vectorPosteriorFeatureTime i) hi]

theorem vectorJoint_weightedOverlap_variance_le_integrated_covariance {n k : ℕ}
    (hn : 0 < n) (s : RSBScheme k) (β t a : ℝ) (hβ : β≠0) (ht : t < 1)
    (hq : s.q 1=0) (ha : a ≤ s.m 1) (kernel : ℝ → ℝ) :
    variance (fun p : VectorGaussianSpace n k × Configuration n =>
      vectorEuclideanWeightedOverlapScore s β t a kernel p.2 p.1) (vectorEuclideanJointLaw s β t a) ≤
      (∑ i,vectorPosteriorFeatureWeight s a i*(vectorPosteriorFeatureKernel s kernel i)^2*
        ∫p : VectorGaussianSpace n k × Configuration n,
          Matrix.trace (vectorFieldHessianMatrix s β t (vectorPosteriorFeatureTime i)
              (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) p.1)*
            vectorSpinCovariance s β t (vectorPosteriorFeatureTime i)
              (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) p.1))
          ∂vectorEuclideanJointLaw s β t a)/(n : ℝ)^2 := by
  rw [←integral_vectorWeightedHessianEnergy_eq_trace s β t a kernel]
  exact vectorJoint_weightedOverlap_variance_le_hessian_energy hn s β t a hβ ht hq ha kernel

end QuantitativePaper
