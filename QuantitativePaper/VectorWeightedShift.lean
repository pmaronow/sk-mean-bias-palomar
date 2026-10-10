module
public import QuantitativePaper.VectorShiftEnergy
public import QuantitativePaper.VectorPosteriorMetric

@[expose] public section

/-! Actual finite Stieltjes gradient and inverse-metric bound for the
weighted overlap observable. All feature Hessians and shift vectors are
constructed from the actual potential and its Gaussian coordinates. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

def vectorPosteriorFeatureFinTime {k : ℕ} (i : vectorPosteriorFeatureIndex k) : Fin (k+3) :=
  ⟨vectorPosteriorFeatureTime i,by cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega⟩

def vectorPosteriorFeatureKernel {k : ℕ} (s : RSBScheme k) (kernel : ℝ → ℝ)
    (i : vectorPosteriorFeatureIndex k) : ℝ := kernel (s.q (vectorPosteriorFeatureTime i))

def vectorPosteriorScoreShift {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (σ : Configuration n) (z : VectorGaussianSpace n k) (i : vectorPosteriorFeatureIndex k) :
    VectorGaussianSpace n k := vectorEuclideanScoreShift s β t σ (vectorPosteriorFeatureFinTime i) z

theorem vectorEuclideanWeightedOverlapScore_eq_feature_sum {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (kernel : ℝ → ℝ) (σ : Configuration n) :
    vectorEuclideanWeightedOverlapScore s β t a kernel σ=fun z =>
      ∑ i,vectorPosteriorFeatureWeight s a i*vectorPosteriorFeatureKernel s kernel i*
        vectorEuclideanOverlapScore s β t σ (vectorPosteriorFeatureTime i) z := by
  classical
  funext z
  rw [Fintype.sum_option]
  simp only [vectorPosteriorFeatureWeight,vectorPosteriorFeatureKernel,vectorPosteriorFeatureTime,
    vectorEuclideanWeightedOverlapScore]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (s.m (i+2)-s.m (i+1))*kernel (s.q (i+2))*
    vectorEuclideanOverlapScore s β t σ (i+2) z)]

theorem vectorEuclideanWeightedOverlapScore_gradient_shift {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β t a : ℝ) (hβ : β≠0) (ht : t < 1)
    (kernel : ℝ → ℝ) (σ : Configuration n) (z : VectorGaussianSpace n k) :
    posteriorFeatureShift (vectorPosteriorFeatureHessian s β t z)
      (vectorPosteriorFeatureWeight s a) (vectorPosteriorFeatureKernel s kernel)
      (vectorPosteriorScoreShift s β t σ z)=
      (n : ℝ) • gradient (vectorEuclideanWeightedOverlapScore s β t a kernel σ) z := by
  classical
  rw [vectorEuclideanWeightedOverlapScore_eq_feature_sum,gradient_finite_sum]
  · simp_rw [gradient_const_mul _
      ((boundedJets_vectorEuclideanOverlapScore s β t σ _).1.differentiable (by simp))]
    unfold posteriorFeatureShift vectorPosteriorFeatureHessian vectorPosteriorScoreShift
    have ht' (i : vectorPosteriorFeatureIndex k) :
        hessianOperator (vectorEuclideanHistoryPotential s β t (vectorPosteriorFeatureTime i)) z
          (vectorEuclideanScoreShift s β t σ (vectorPosteriorFeatureFinTime i) z)=
        (n : ℝ) • gradient (vectorEuclideanOverlapScore s β t σ (vectorPosteriorFeatureTime i)) z :=
      vectorEuclideanOverlapScore_hessian_shift_all hn s β t hβ ht σ (vectorPosteriorFeatureFinTime i) z
    simp_rw [ht',smul_comm _ (n : ℝ)]
    rw [Finset.smul_sum]
  · intro i _
    exact (contDiff_const.mul (boundedJets_vectorEuclideanOverlapScore s β t σ _).1).differentiable (by simp)

theorem vectorEuclideanWeightedOverlapScore_inverse_energy_le {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β t a : ℝ) (hβ : β≠0) (ht : t < 1) (ha : a ≤ s.m 1)
    (kernel : ℝ → ℝ) (σ : Configuration n) (z : VectorGaussianSpace n k) :
    inner ℝ (gradient (vectorEuclideanWeightedOverlapScore s β t a kernel σ) z)
      (Ring.inverse (hessianOperator (vectorPosteriorPotential s β t a σ) z)
        (gradient (vectorEuclideanWeightedOverlapScore s β t a kernel σ) z)) ≤
      (∑ i,vectorPosteriorFeatureWeight s a i*(vectorPosteriorFeatureKernel s kernel i)^2*
        inner ℝ (spinVector σ-vectorEuclideanMagnetization s β t (vectorPosteriorFeatureTime i) z)
          (vectorFieldHessian s β t (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) z).1
            (k+2-vectorPosteriorFeatureTime i)
            (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) z).2
            (spinVector σ-vectorEuclideanMagnetization s β t (vectorPosteriorFeatureTime i) z)))/(n : ℝ)^2 := by
  classical
  have hN : 0 < (n : ℝ)^2 := sq_pos_of_pos (by positivity)
  have hh := vectorPosteriorFeature_inverse_energy_le s β t a ha σ z
    (vectorPosteriorFeatureKernel s kernel) (vectorPosteriorScoreShift s β t σ z)
  rw [vectorEuclideanWeightedOverlapScore_gradient_shift hn s β t a hβ ht kernel σ z] at hh
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right] at hh
  apply (le_div_iff₀ hN).mpr
  calc
    _ ≤ ∑ i,vectorPosteriorFeatureWeight s a i*(vectorPosteriorFeatureKernel s kernel i)^2*
        inner ℝ (vectorPosteriorScoreShift s β t σ z i)
          (vectorPosteriorFeatureHessian s β t z i (vectorPosteriorScoreShift s β t σ z i)) := by
      convert hh using 1 <;> ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (vectorEuclideanScoreShift_energy_le s β t hβ ht σ (vectorPosteriorFeatureFinTime i) z)
      (mul_nonneg (vectorPosteriorFeatureWeight_nonneg s a ha i) (sq_nonneg _))

end QuantitativePaper
