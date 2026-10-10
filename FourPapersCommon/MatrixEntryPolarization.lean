module
public import FourPapersCommon.EuclideanOperatorMatrix

@[expose] public section

/-! Exact finite-basis polarization of real symmetric matrix entries. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 800000

def euclideanMatrixQuadratic (A : Matrix (Fin n) (Fin n) ℝ)
    (w : EuclideanSpace ℝ (Fin n)) : ℝ := ∑i : Fin n, ∑j : Fin n, A i j*w i*w j

theorem euclideanMatrixQuadratic_single (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    euclideanMatrixQuadratic A (EuclideanSpace.single i 1) = A i i := by
  simp [euclideanMatrixQuadratic, EuclideanSpace.single_apply, mul_ite, ite_mul]

theorem euclideanMatrixQuadratic_polarization (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    euclideanMatrixQuadratic A (EuclideanSpace.single i 1+EuclideanSpace.single j 1) -
      euclideanMatrixQuadratic A (EuclideanSpace.single i 1) -
      euclideanMatrixQuadratic A (EuclideanSpace.single j 1) = A i j+A j i := by
  simp only [euclideanMatrixQuadratic, PiLp.add_apply, EuclideanSpace.single_apply,
    mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero,
    add_zero, zero_add]
  ring

theorem euclideanMatrixQuadratic_entry (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀i j, A i j=A j i) (i j : Fin n) :
    A i j = (euclideanMatrixQuadratic A (EuclideanSpace.single i 1+EuclideanSpace.single j 1) -
      euclideanMatrixQuadratic A (EuclideanSpace.single i 1) -
      euclideanMatrixQuadratic A (EuclideanSpace.single j 1))/2 := by
  rw [euclideanMatrixQuadratic_polarization, hs j i]
  ring

end FourPapersCommon
