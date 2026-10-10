module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section

/-! Entrywise Cauchy–Schwarz and the sharp trace-square bound for a genuine
positive semidefinite real matrix. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem positive_matrix_entry_square_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (i j : ι) : (C i j)^2≤C i i*C j j := by
  have hsym : C j i=C i j:=by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hC.1 i) j
  have hq : ∀x : ℝ,0≤C i i*(x*x)+(2*C i j)*x+C j j:=by
    intro x
    have hh:=hC.dotProduct_mulVec_nonneg (x • Pi.single i 1+Pi.single j 1)
    simp [Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,add_dotProduct,
      smul_dotProduct,dotProduct_smul,Matrix.mulVec_single,single_dotProduct,
      Pi.smul_apply,smul_eq_mul,hsym] at hh
    nlinarith
  have hd:=discrim_le_zero hq
  unfold discrim at hd
  nlinarith

theorem positive_matrix_trace_square_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) : Matrix.trace (C*C)≤(Matrix.trace C)^2 := by
  have hsym (i j : ι) : C j i=C i j:=by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hC.1 i) j
  calc
    Matrix.trace (C*C)=∑i : ι,∑j : ι,(C i j)^2:=by
      unfold Matrix.trace
      simp only [Matrix.diag_apply,Matrix.mul_apply,hsym,pow_two]
    _≤∑i : ι,∑j : ι,C i i*C j j:=
      Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>positive_matrix_entry_square_le C hC i j
    _=(Matrix.trace C)^2:=by
      unfold Matrix.trace
      simp only [Matrix.diag_apply,pow_two,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]

end FourPapersCommon
