module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact finite Stieltjes summation by parts. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon

theorem finite_weighted_differences (a f : ℕ→ℝ) (N : ℕ) :
    (∑p∈Finset.range N,a p*(f p-f (p+1)))+
      (∑p∈Finset.range N,(a p-a (p+1))*f (p+1))=a 0*f 0-a N*f N := by
  rw [←Finset.sum_add_distrib]
  calc
    _=∑p∈Finset.range N,(a p*f p-a (p+1)*f (p+1)) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _=_:=Finset.sum_range_sub' _ _

end FourPapersCommon
