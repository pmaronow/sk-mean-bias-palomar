module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Finite cell-difference telescoping with literal node jumps. -/
namespace FourPapersCommon
open scoped BigOperators

theorem sum_cell_differences_with_jumps (F : ℕ→ℝ→ℝ) (Q : ℕ→ℝ) (N : ℕ) :
    (∑i∈Finset.range (N+1),(F i (Q (i+1))-F i (Q i)))=
      F N (Q (N+1))-F 0 (Q 0)-
        ∑i∈Finset.range N,(F (i+1) (Q (i+1))-F i (Q (i+1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
    ring

theorem sum_cell_differences_of_match (F : ℕ→ℝ→ℝ) (Q : ℕ→ℝ) (N : ℕ)
    (h : ∀i<N,F (i+1) (Q (i+1))=F i (Q (i+1))) :
    (∑i∈Finset.range (N+1),(F i (Q (i+1))-F i (Q i)))=
      F N (Q (N+1))-F 0 (Q 0) := by
  rw [sum_cell_differences_with_jumps]
  have hz : (∑i∈Finset.range N,(F (i+1) (Q (i+1))-F i (Q (i+1))))=0:=by
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i (Finset.mem_range.mp hi),sub_self]
  rw [hz,sub_zero]

end FourPapersCommon
