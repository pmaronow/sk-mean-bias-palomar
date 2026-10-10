module
public import QuantitativeFollowup.AnisotropicFieldDerivative
public import QuantitativeFollowup.AnisotropicSelfOverlapScore
public import QuantitativeFollowup.MeanSquareHessianShift

@[expose] public section

/-! Actual selected-coordinate Hessian shift and quadratic energy, for
all anisotropic revealed fields. No score derivative is supplied as a
hypothesis; it is derived from the literal Gaussian-history right inverse. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

abbrev AnisotropicSelectedField (J : Finset (Fin n)) := EuclideanSpace ℝ J

def anisotropicSelectedProjection (J : Finset (Fin n)) : Field n→L[ℝ]AnisotropicSelectedField J :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => ℝ)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun l : J => EuclideanSpace.proj l.val)

def anisotropicSelectedInsertion (J : Finset (Fin n)) : AnisotropicSelectedField J→L[ℝ]Field n :=
  ∑l : J,ContinuousLinearMap.smulRight (EuclideanSpace.proj l) (EuclideanSpace.single l.val 1)

@[simp] theorem anisotropicSelectedProjection_apply (J : Finset (Fin n)) (w : Field n) (l : J) :
    anisotropicSelectedProjection J w l=w l.val := rfl

theorem inner_anisotropicSelectedInsertion (J : Finset (Fin n)) (v : Field n)
    (w : AnisotropicSelectedField J) :
    inner ℝ v (anisotropicSelectedInsertion J w)=inner ℝ (anisotropicSelectedProjection J v) w := by
  rw [anisotropicSelectedInsertion,sum_apply,inner_sum]
  simp only [ContinuousLinearMap.smulRight_apply,real_inner_smul_right]
  simp [PiLp.inner_apply,RCLike.inner_apply,Pi.single_apply,mul_comm]

def anisotropicSelectedMagnetization (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) : AnisotropicGaussianSpace n k→AnisotropicSelectedField J :=
  anisotropicSelectedProjection J ∘ anisotropicEuclideanMagnetization D s i

theorem contDiff_anisotropicSelectedMagnetization (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) : ContDiff ℝ ∞ (anisotropicSelectedMagnetization D s J i) :=
  (anisotropicSelectedProjection J).contDiff.comp (contDiff_anisotropicEuclideanMagnetization D s i)

theorem anisotropicEuclideanSelfOverlapScore_eq_meanSquare (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) :
    anisotropicEuclideanSelfOverlapScore D s J i=
      normalizedMeanSquare (anisotropicSelectedMagnetization D s J i) (J.card : ℝ) := by
  funext z
  rw [normalizedMeanSquare,EuclideanSpace.real_norm_sq_eq]
  simp only [anisotropicEuclideanSelfOverlapScore,anisotropicSelectedMagnetization,
    Function.comp_def,anisotropicSelectedProjection_apply]
  congr 1
  exact (Finset.sum_coe_sort J (fun l : Fin n => (anisotropicEuclideanMagnetization D s i z l)^2)).symm

def anisotropicEuclideanSelfOverlapShift (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : Fin (k+3)) (z : AnisotropicGaussianSpace n k) : AnisotropicGaussianSpace n k :=
  anisotropicEuclideanFieldRightInverse D s i
    (anisotropicSelectedInsertion J (anisotropicSelectedMagnetization D s J i z))

theorem anisotropicEuclideanSelfOverlapScore_hessian_shift (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (i : Fin (k+3)) (hi : 0 < s.q i) (z : AnisotropicGaussianSpace n k) :
    hessianOperator (anisotropicEuclideanHistoryPotential D s i) z
      (anisotropicEuclideanSelfOverlapShift D s J i z)=
      ((J.card : ℝ)/2) • gradient (anisotropicEuclideanSelfOverlapScore D s J i) z := by
  rw [anisotropicEuclideanSelfOverlapScore_eq_meanSquare]
  apply normalizedMeanSquare_hessian_shift _ _
    ((anisotropicEuclideanFieldRightInverse D s i).comp (anisotropicSelectedInsertion J))
    ((contDiff_anisotropicEuclideanHistoryPotential D s i).of_le (by simp))
    ((contDiff_anisotropicSelectedMagnetization D s J i).of_le (by simp))
    (fun y w => ?_) (J.card : ℝ) (by exact_mod_cast hJ.card_pos.ne') z
  rw [ContinuousLinearMap.comp_apply,anisotropicEuclideanHistoryPotential_rightInverse_deriv D s i hi,
    inner_anisotropicSelectedInsertion]
  rfl

theorem anisotropicEuclideanSelfOverlapScore_zero_overlap (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : Fin (k+3)) (hi : s.q i=0) :
    anisotropicEuclideanSelfOverlapScore D s J i=fun _ => 0 := by
  funext z
  simp only [anisotropicEuclideanSelfOverlapScore,anisotropicEuclideanMagnetization_zero_overlap D s i hi,
    PiLp.zero_apply,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,zero_div]

theorem anisotropicEuclideanSelfOverlapShift_zero_overlap (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : Fin (k+3)) (hi : s.q i=0)
    (z : AnisotropicGaussianSpace n k) : anisotropicEuclideanSelfOverlapShift D s J i z=0 := by
  simp [anisotropicEuclideanSelfOverlapShift,anisotropicSelectedMagnetization,
    anisotropicEuclideanMagnetization_zero_overlap D s i hi]

theorem anisotropicEuclideanSelfOverlapScore_hessian_shift_all (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (i : Fin (k+3)) (z : AnisotropicGaussianSpace n k) :
    hessianOperator (anisotropicEuclideanHistoryPotential D s i) z
      (anisotropicEuclideanSelfOverlapShift D s J i z)=
      ((J.card : ℝ)/2) • gradient (anisotropicEuclideanSelfOverlapScore D s J i) z := by
  by_cases hi : 0 < s.q i
  · exact anisotropicEuclideanSelfOverlapScore_hessian_shift D s J hJ i hi z
  · have hi0 : s.q i=0 := le_antisymm (le_of_not_gt hi) (s.q_nonneg (by omega))
    rw [anisotropicEuclideanSelfOverlapShift_zero_overlap D s J i hi0,
      anisotropicEuclideanSelfOverlapScore_zero_overlap D s J i hi0]
    simp [gradient_fun_const]

end QuantitativeFollowup
