module
public import QuantitativeFollowup.AnisotropicSelectedShift

@[expose] public section

/-! Literal selected-coordinate quadratic Hessian energy of the actual
anisotropic Gaussian field. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

def anisotropicFieldHessian (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) : Field n→L[ℝ]Field n :=
  hessianOperator (fun w => anisotropicFinitePotential D s j (P+anisotropicFieldInjection n w)) 0

theorem contDiff_anisotropicTranslatedFieldPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    ContDiff ℝ ∞ (fun w => anisotropicFinitePotential D s j (P+anisotropicFieldInjection n w)) :=
  (contDiff_anisotropicFinitePotential D s j).comp (contDiff_const.add (anisotropicFieldInjection n).contDiff)

theorem anisotropicFieldHessian_quadratic_nonneg (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    0 ≤ inner ℝ w (anisotropicFieldHessian D s j P w) := by
  have he : (fun r : ℝ => anisotropicFinitePotential D s j
      (P+anisotropicFieldInjection n (0+r • w)))=
      fun r => anisotropicFinitePotential D s j (P+r • anisotropicFieldInjection n w) := by
    funext r
    rw [zero_add,map_smul]
  rw [real_inner_comm,anisotropicFieldHessian,inner_hessianOperator]
  change 0 ≤ directionalHessian (fun v => anisotropicFinitePotential D s j (P+anisotropicFieldInjection n v)) 0 w
  rw [directionalHessian_eq_secondDeriv_line _
    ((contDiff_anisotropicTranslatedFieldPotential D s j P).of_le (by simp)),he,
    ←directionalHessian_eq_secondDeriv_line _ ((contDiff_anisotropicFinitePotential D s j).of_le (by simp))]
  exact directionalHessian_nonneg_of_convex _ ((contDiff_anisotropicFinitePotential D s j).of_le (by simp))
    (convexOn_anisotropicFinitePotential D s j) P (anisotropicFieldInjection n w)

def anisotropicSelectedMean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) (z : AnisotropicGaussianSpace n k) : Field n :=
  anisotropicSelectedInsertion J (anisotropicSelectedMagnetization D s J i z)

def anisotropicSelfOverlapEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) (z : AnisotropicGaussianSpace n k) : ℝ :=
  inner ℝ (anisotropicSelectedMean D s J i z)
    (anisotropicFieldHessian D s (k+2-i) (anisotropicEuclideanStateLinear D s i z)
      (anisotropicSelectedMean D s J i z))

theorem anisotropicEuclideanSelfOverlapShift_energy_eq (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : Fin (k+3)) (hi : 0 < s.q i)
    (z : AnisotropicGaussianSpace n k) :
    inner ℝ (anisotropicEuclideanSelfOverlapShift D s J i z)
      (hessianOperator (anisotropicEuclideanHistoryPotential D s i) z
        (anisotropicEuclideanSelfOverlapShift D s J i z))=anisotropicSelfOverlapEnergy D s J i z := by
  let L := anisotropicEuclideanStateLinear D s i
  let w := anisotropicSelectedMean D s J i z
  let v := anisotropicEuclideanSelfOverlapShift D s J i z
  have hv : L v=anisotropicFieldInjection n w := anisotropicEuclideanStateLinear_rightInverse D s i hi w
  have he : (fun r : ℝ => anisotropicEuclideanHistoryPotential D s i (z+r • v))=
      fun r => anisotropicFinitePotential D s (k+2-i) (L z+anisotropicFieldInjection n (0+r • w)) := by
    funext r
    change anisotropicFinitePotential D s (k+2-i) (L (z+r • v))=_
    rw [map_add,map_smul,hv,zero_add,map_smul]
  rw [real_inner_comm,inner_hessianOperator]
  unfold anisotropicSelfOverlapEnergy anisotropicFieldHessian
  conv_rhs => rw [real_inner_comm]
  rw [inner_hessianOperator]
  change directionalHessian (anisotropicEuclideanHistoryPotential D s i) z v=
    directionalHessian (fun y => anisotropicFinitePotential D s (k+2-i) (L z+anisotropicFieldInjection n y)) 0 w
  rw [directionalHessian_eq_secondDeriv_line _
    ((contDiff_anisotropicEuclideanHistoryPotential D s i).of_le (by simp)),he,
    ←directionalHessian_eq_secondDeriv_line _
      ((contDiff_anisotropicTranslatedFieldPotential D s (k+2-i) (L z)).of_le (by simp))]

theorem anisotropicEuclideanSelfOverlapShift_energy_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : Fin (k+3)) (z : AnisotropicGaussianSpace n k) :
    inner ℝ (anisotropicEuclideanSelfOverlapShift D s J i z)
      (hessianOperator (anisotropicEuclideanHistoryPotential D s i) z
        (anisotropicEuclideanSelfOverlapShift D s J i z))≤anisotropicSelfOverlapEnergy D s J i z := by
  by_cases hi : 0 < s.q i
  · exact (anisotropicEuclideanSelfOverlapShift_energy_eq D s J i hi z).le
  · have hi0 : s.q i=0 := le_antisymm (le_of_not_gt hi) (s.q_nonneg (by omega))
    rw [anisotropicEuclideanSelfOverlapShift_zero_overlap D s J i hi0]
    simp only [map_zero,inner_zero_left]
    exact anisotropicFieldHessian_quadratic_nonneg _ _ _ _ _

end QuantitativeFollowup
