module
public import QuantitativeFollowup.AnisotropicPosterior
public import QuantitativePaper.PosteriorMetricCalculus

@[expose] public section

/-! The posterior Hessian is literally identity plus the weighted Hessians
of the retained vector potentials. These features are genuinely positive
semidefinite and symmetric. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets QuantitativePaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

abbrev anisotropicPosteriorFeatureIndex (k : ℕ) := Option (Fin k)

def anisotropicPosteriorFeatureTime {k : ℕ} : anisotropicPosteriorFeatureIndex k → ℕ
  | none => 1
  | some i => i+2

def anisotropicPosteriorFeatureWeight {k : ℕ} (s : RSBScheme k) (a : ℝ) :
    anisotropicPosteriorFeatureIndex k → ℝ
  | none => s.m 1-a
  | some i => s.m (i+2)-s.m (i+1)

def anisotropicPosteriorFeatureHessian {n k : ℕ} (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (x : AnisotropicGaussianSpace n k) (i : anisotropicPosteriorFeatureIndex k) :
    AnisotropicGaussianSpace n k →L[ℝ] AnisotropicGaussianSpace n k :=
  hessianOperator (anisotropicEuclideanHistoryPotential D s (anisotropicPosteriorFeatureTime i)) x

theorem anisotropicPosteriorFeatureWeight_nonneg {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (ha : a ≤ s.m 1) (i : anisotropicPosteriorFeatureIndex k) :
    0 ≤ anisotropicPosteriorFeatureWeight s a i := by
  cases i with
  | none => exact sub_nonneg.mpr ha
  | some i => exact vectorStieltjesCoefficient_nonneg s i.isLt

theorem anisotropicPosteriorFeatureHessian_nonneg {n k : ℕ} (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (x : AnisotropicGaussianSpace n k) (i : anisotropicPosteriorFeatureIndex k)
    (z : AnisotropicGaussianSpace n k) :
    0 ≤ inner ℝ z (anisotropicPosteriorFeatureHessian D s x i z) := by
  rw [real_inner_comm,anisotropicPosteriorFeatureHessian,inner_hessianOperator]
  exact directionalHessian_nonneg_of_convex _
    ((contDiff_anisotropicEuclideanHistoryPotential D s _).of_le (by simp))
    (convexOn_anisotropicEuclideanHistoryPotential D s _) x z

theorem anisotropicPosteriorFeatureHessian_symmetric {n k : ℕ} (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (x : AnisotropicGaussianSpace n k) (i : anisotropicPosteriorFeatureIndex k)
    (z w : AnisotropicGaussianSpace n k) :
    inner ℝ z (anisotropicPosteriorFeatureHessian D s x i w)=
      inner ℝ w (anisotropicPosteriorFeatureHessian D s x i z) := by
  conv_lhs => rw [real_inner_comm]
  conv_rhs => rw [real_inner_comm]
  rw [anisotropicPosteriorFeatureHessian,
    inner_hessianOperator,inner_hessianOperator]
  have hh := (contDiff_anisotropicEuclideanHistoryPotential (n := n) D s
    (anisotropicPosteriorFeatureTime i)).contDiffAt (x := x) |>.isSymmSndFDerivAt (by simp)
  exact hh.eq w z

theorem anisotropicPosteriorPotential_hessian_metric {n k : ℕ} (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (σ : Configuration n) (x : AnisotropicGaussianSpace n k) :
    hessianOperator (anisotropicPosteriorPotential D s a σ) x=
      posteriorFeatureHessian (anisotropicPosteriorFeatureHessian D s x)
        (anisotropicPosteriorFeatureWeight s a) := by
  classical
  let L := anisotropicEuclideanTerminalLinear (n := n) D s σ
  let U := anisotropicEuclideanHistoryPotential (n := n) D s
  have hu (i : ℕ) : ContDiff ℝ 2 (U i) :=
    (contDiff_anisotropicEuclideanHistoryPotential D s i).of_le (by simp)
  have he : anisotropicPosteriorPotential (n := n) D s a σ=fun y =>
      ((FourPapersCommon.standardGaussianPotential y+(-1)*L y)+(s.m 1-a)*U 1 y)+
        (∑ i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*U (i+2) y)+
        Real.log (anisotropicFiniteOuterPartition (n := n) D s a) := by
    funext y
    unfold anisotropicPosteriorPotential
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
    simp only [anisotropicPosteriorFeatureWeight,anisotropicPosteriorFeatureHessian,anisotropicPosteriorFeatureTime]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      (s.m (i+2)-s.m (i+1)) • hessianOperator (anisotropicEuclideanHistoryPotential D s (i+2)) x)]
    dsimp [U]
    abel
  · intro i _
    exact contDiff_const.mul (hu (i+2))

theorem anisotropicPosteriorPotential_hessian_isUnit {n k : ℕ} (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (σ : Configuration n) (x : AnisotropicGaussianSpace n k) :
    IsUnit (hessianOperator (anisotropicPosteriorPotential D s a σ) x) := by
  rw [anisotropicPosteriorPotential_hessian_metric]
  exact posteriorFeatureHessian_isUnit _ _ (anisotropicPosteriorFeatureWeight_nonneg s a ha)
    (anisotropicPosteriorFeatureHessian_nonneg D s x)

theorem anisotropicPosteriorFeature_inverse_energy_le {n k : ℕ} (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (σ : Configuration n) (x : AnisotropicGaussianSpace n k)
    (kernel : anisotropicPosteriorFeatureIndex k → ℝ)
    (ζ : anisotropicPosteriorFeatureIndex k → AnisotropicGaussianSpace n k) :
    inner ℝ (posteriorFeatureShift (anisotropicPosteriorFeatureHessian D s x)
      (anisotropicPosteriorFeatureWeight s a) kernel ζ)
      (Ring.inverse (hessianOperator (anisotropicPosteriorPotential D s a σ) x)
        (posteriorFeatureShift (anisotropicPosteriorFeatureHessian D s x)
          (anisotropicPosteriorFeatureWeight s a) kernel ζ)) ≤
      ∑ i,anisotropicPosteriorFeatureWeight s a i*(kernel i)^2*
        inner ℝ (ζ i) (anisotropicPosteriorFeatureHessian D s x i (ζ i)) := by
  rw [anisotropicPosteriorPotential_hessian_metric]
  exact posteriorFeature_inverse_energy_le _ _ _ _
    (anisotropicPosteriorFeatureWeight_nonneg s a ha)
    (anisotropicPosteriorFeatureHessian_nonneg D s x)
    (anisotropicPosteriorFeatureHessian_symmetric D s x)

end QuantitativeFollowup
