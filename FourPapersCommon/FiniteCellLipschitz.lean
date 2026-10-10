module
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! A genuine finite-cell Lipschitz estimate pastes across repeated nodes
and partial initial/final cells. No derivative at a joining node is needed. -/
noncomputable section
open Set
open scoped BigOperators
namespace FourPapersCommon

theorem norm_sub_le_of_finite_interval_bounds {G : Type*} [NormedAddCommGroup G]
    (F : ℝ→G) (Q : ℕ→ℝ) (N : ℕ) (hQ0 : Q 0=0) (hQN : Q N=1)
    (hQ : ∀i,i<N→Q i≤Q (i+1)) (C : ℝ)
    (hcell : ∀i,i<N→∀{a b : ℝ},Q i≤a→a≤b→b≤Q (i+1)→
      ‖F b-F a‖≤C*(b-a))
    {r q : ℝ} (hr : r∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) 1) (hrq : r≤q) :
    ‖F q-F r‖≤C*(q-r) := by
  let T:=fun i=>max r (min q (Q i))
  have hT0:T 0=r:=by
    simp only [T,hQ0,min_eq_right hq.1,max_eq_left hr.1]
  have hTN:T N=q:=by simp only [T,hQN,min_eq_left hq.2,max_eq_right hrq]
  have hTq (i : ℕ):T i≤q:=max_le hrq (min_le_left _ _)
  have hrT (i : ℕ):r≤T i:=le_max_left _ _
  have hstep (i : ℕ) (hi : i<N):T i≤T (i+1):=
    max_le_max le_rfl (min_le_min le_rfl (hQ i hi))
  have hbound (i : ℕ) (hi : i<N):‖F (T (i+1))-F (T i)‖≤C*(T (i+1)-T i):=by
    rcases eq_or_lt_of_le (hstep i hi) with he|he
    · simp [he]
    have hlow:Q i≤T i:=by
      by_cases h:Q i≤q
      · simpa only [T,min_eq_right h] using le_max_right r (Q i)
      · have hh:T i=q:=by simp only [T,min_eq_left (le_of_not_ge h),max_eq_right hrq]
        exact False.elim (not_lt_of_ge (hTq (i+1)) (hh ▸ he))
    have hupp:T (i+1)≤Q (i+1):=by
      by_cases h:r≤Q (i+1)
      · exact max_le h (min_le_right _ _)
      · have hh:T (i+1)=r:=max_eq_left ((min_le_right _ _).trans (le_of_not_ge h))
        exact False.elim (not_lt_of_ge (hrT i) (hh ▸ he))
    exact hcell i hi hlow (hstep i hi) hupp
  rw [←hTN,←hT0,←Finset.sum_range_sub (fun i=>F (T i)) N]
  calc
    _≤∑i∈Finset.range N,‖F (T (i+1))-F (T i)‖:=norm_sum_le _ _
    _≤∑i∈Finset.range N,C*(T (i+1)-T i):=
      Finset.sum_le_sum fun i hi=>hbound i (Finset.mem_range.mp hi)
    _=C*(T N-T 0):=by rw [←Finset.mul_sum,Finset.sum_range_sub]

end FourPapersCommon
