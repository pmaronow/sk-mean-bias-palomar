module
public import QuantitativePaper.PosteriorMetricCalculus

@[expose] public section

/-! The posterior Hessian is literally identity plus the weighted Hessians
of the retained vector potentials. These features are genuinely positive
semidefinite and symmetric. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

abbrev vectorPosteriorFeatureIndex (k : ℕ) := Option (Fin k)

def vectorPosteriorFeatureTime {k : ℕ} : vectorPosteriorFeatureIndex k → ℕ
  | none => 1
  | some i => i+2

def vectorPosteriorFeatureWeight {k : ℕ} (s : RSBScheme k) (a : ℝ) :
    vectorPosteriorFeatureIndex k → ℝ
  | none => s.m 1-a
  | some i => s.m (i+2)-s.m (i+1)

def vectorPosteriorFeatureHessian {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (x : VectorGaussianSpace n k) (i : vectorPosteriorFeatureIndex k) :
    VectorGaussianSpace n k →L[ℝ] VectorGaussianSpace n k :=
  hessianOperator (vectorEuclideanHistoryPotential s β t (vectorPosteriorFeatureTime i)) x

theorem vectorPosteriorFeatureWeight_nonneg {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (ha : a ≤ s.m 1) (i : vectorPosteriorFeatureIndex k) :
    0 ≤ vectorPosteriorFeatureWeight s a i := by
  cases i with
  | none => exact sub_nonneg.mpr ha
  | some i => exact vectorStieltjesCoefficient_nonneg s i.isLt

theorem vectorPosteriorFeatureHessian_nonneg {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (x : VectorGaussianSpace n k) (i : vectorPosteriorFeatureIndex k)
    (z : VectorGaussianSpace n k) :
    0 ≤ inner ℝ z (vectorPosteriorFeatureHessian s β t x i z) := by
  rw [real_inner_comm,vectorPosteriorFeatureHessian,inner_hessianOperator]
  exact directionalHessian_nonneg_of_convex _
    ((contDiff_vectorEuclideanHistoryPotential s β t _).of_le (by simp))
    (convexOn_vectorEuclideanHistoryPotential s β t _) x z

theorem vectorPosteriorFeatureHessian_symmetric {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (x : VectorGaussianSpace n k) (i : vectorPosteriorFeatureIndex k)
    (z w : VectorGaussianSpace n k) :
    inner ℝ z (vectorPosteriorFeatureHessian s β t x i w)=
      inner ℝ w (vectorPosteriorFeatureHessian s β t x i z) := by
  conv_lhs => rw [real_inner_comm]
  conv_rhs => rw [real_inner_comm]
  rw [vectorPosteriorFeatureHessian,
    inner_hessianOperator,inner_hessianOperator]
  have hh := (contDiff_vectorEuclideanHistoryPotential (n := n) s β t
    (vectorPosteriorFeatureTime i)).contDiffAt (x := x) |>.isSymmSndFDerivAt (by simp)
  exact hh.eq w z

theorem vectorPosteriorPotential_hessian_metric {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (σ : Configuration n) (x : VectorGaussianSpace n k) :
    hessianOperator (vectorPosteriorPotential s β t a σ) x=
      posteriorFeatureHessian (vectorPosteriorFeatureHessian s β t x)
        (vectorPosteriorFeatureWeight s a) := by
  classical
  let L := vectorEuclideanTerminalLinear (n := n) s β t σ
  let U := vectorEuclideanHistoryPotential (n := n) s β t
  have hu (i : ℕ) : ContDiff ℝ 2 (U i) :=
    (contDiff_vectorEuclideanHistoryPotential s β t i).of_le (by simp)
  have he : vectorPosteriorPotential (n := n) s β t a σ=fun y =>
      ((FourPapersCommon.standardGaussianPotential y+(-1)*L y)+(s.m 1-a)*U 1 y)+
        (∑ i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*U (i+2) y)+
        Real.log (vectorOuterPartition (n := n) s β t a) := by
    funext y
    rw [vectorEuclideanTerminalLinear_apply]
    unfold vectorPosteriorPotential
    dsimp [U]
    ring
  rw [he,hessianOperator_add_const]
  rw [hessianOperator_add _ _
    (((contDiff_standardGaussianPotential.of_le (by simp)).add
      (contDiff_const.mul L.contDiff)).add (contDiff_const.mul (hu 1)))
    (ContDiff.sum (fun i _ => contDiff_const.mul (hu (i+2))))]
  rw [hessianOperator_add _ _
    ((contDiff_standardGaussianPotential.of_le (by simp)).add (contDiff_const.mul L.contDiff))
    (contDiff_const.mul (hu 1)),
    hessianOperator_add _ _ (contDiff_standardGaussianPotential.of_le (by simp))
      (contDiff_const.mul L.contDiff),
    hessianOperator_standardGaussianPotential,hessianOperator_const_mul L L.contDiff,
    hessianOperator_linear,smul_zero,add_zero,
    hessianOperator_const_mul _ (hu 1),hessianOperator_finite_sum]
  · simp_rw [hessianOperator_const_mul _ (hu _)]
    unfold posteriorFeatureHessian
    rw [Fintype.sum_option]
    simp only [vectorPosteriorFeatureWeight,vectorPosteriorFeatureHessian,vectorPosteriorFeatureTime]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      (s.m (i+2)-s.m (i+1)) • hessianOperator (vectorEuclideanHistoryPotential s β t (i+2)) x)]
    dsimp [U]
    abel
  · intro i _
    exact contDiff_const.mul (hu (i+2))

theorem vectorPosteriorPotential_hessian_isUnit {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ha : a ≤ s.m 1) (σ : Configuration n) (x : VectorGaussianSpace n k) :
    IsUnit (hessianOperator (vectorPosteriorPotential s β t a σ) x) := by
  rw [vectorPosteriorPotential_hessian_metric]
  exact posteriorFeatureHessian_isUnit _ _ (vectorPosteriorFeatureWeight_nonneg s a ha)
    (vectorPosteriorFeatureHessian_nonneg s β t x)

theorem vectorPosteriorFeature_inverse_energy_le {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ha : a ≤ s.m 1) (σ : Configuration n) (x : VectorGaussianSpace n k)
    (kernel : vectorPosteriorFeatureIndex k → ℝ)
    (ζ : vectorPosteriorFeatureIndex k → VectorGaussianSpace n k) :
    inner ℝ (posteriorFeatureShift (vectorPosteriorFeatureHessian s β t x)
      (vectorPosteriorFeatureWeight s a) kernel ζ)
      (Ring.inverse (hessianOperator (vectorPosteriorPotential s β t a σ) x)
        (posteriorFeatureShift (vectorPosteriorFeatureHessian s β t x)
          (vectorPosteriorFeatureWeight s a) kernel ζ)) ≤
      ∑ i,vectorPosteriorFeatureWeight s a i*(kernel i)^2*
        inner ℝ (ζ i) (vectorPosteriorFeatureHessian s β t x i (ζ i)) := by
  rw [vectorPosteriorPotential_hessian_metric]
  exact posteriorFeature_inverse_energy_le _ _ _ _
    (vectorPosteriorFeatureWeight_nonneg s a ha)
    (vectorPosteriorFeatureHessian_nonneg s β t x)
    (vectorPosteriorFeatureHessian_symmetric s β t x)

end QuantitativePaper
