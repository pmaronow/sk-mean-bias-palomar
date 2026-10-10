module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

/-! The cumulative covariance of finite Wiener clock increments. -/
open scoped BigOperators
namespace HexagonPaper
set_option maxHeartbeats 600000

theorem clock_increments_nonnegative {n : ℕ} (c : Fin (n+1)→ℝ)
    (hc : Monotone c) (i : Fin n) : 0 ≤ c i.succ-c i.castSucc:=
  sub_nonneg.mpr (hc (by simp [Fin.le_def]))

theorem clock_prefix_sum {n : ℕ} (c : Fin (n+1)→ℝ) (l : Fin (n+1)) :
    (∑i : Fin n,(c i.succ-c i.castSucc)*(if i.val < l.val then 1 else 0))=c l-c 0 :=by
  refine Fin.induction ?_ ?_ l
  · simp
  · intro i hi
    have hmask (j : Fin n) :
        (c j.succ-c j.castSucc)*(if j.val < i.succ.val then 1 else 0)=
          (c j.succ-c j.castSucc)*(if j.val < i.castSucc.val then 1 else 0)+
            (if j=i then c i.succ-c i.castSucc else 0) :=by
      by_cases hji : j=i
      · subst j
        simp
      · have hne : j.val≠i.val:=fun h=>hji (Fin.ext h)
        by_cases hlt : j.val < i.val
        · have hnext : j.val < i.val+1:=by omega
          simp [Fin.val_succ,hlt,hnext,hji]
        · have hnext : ¬j.val < i.val+1:=by omega
          simp [Fin.val_succ,hlt,hnext,hji]
    simp_rw [hmask]
    rw [Finset.sum_add_distrib,hi]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring

theorem clock_prefix_covariance {n : ℕ} (c : Fin (n+1)→ℝ)
    (hc : Monotone c) (h0 : c 0=0) (l r : Fin (n+1)) :
    (∑i : Fin n,(c i.succ-c i.castSucc)*(if i.val < l.val then 1 else 0)*
      (if i.val < r.val then 1 else 0))=min (c l) (c r) :=by
  rcases le_total l r with hlr|hrl
  · rw [min_eq_left (hc hlr)]
    have he (i : Fin n) :
        (c i.succ-c i.castSucc)*(if i.val < l.val then 1 else 0)*
          (if i.val < r.val then 1 else 0)=
        (c i.succ-c i.castSucc)*(if i.val < l.val then 1 else 0):=by
      by_cases hi : i.val < l.val
      · have hir : i.val < r.val:=lt_of_lt_of_le hi hlr
        simp [hi,hir]
      · simp [hi]
    simp_rw [he]
    rw [clock_prefix_sum,h0,sub_zero]
  · rw [min_eq_right (hc hrl)]
    have he (i : Fin n) :
        (c i.succ-c i.castSucc)*(if i.val < l.val then 1 else 0)*
          (if i.val < r.val then 1 else 0)=
        (c i.succ-c i.castSucc)*(if i.val < r.val then 1 else 0):=by
      by_cases hi : i.val < r.val
      · have hil : i.val < l.val:=lt_of_lt_of_le hi hrl
        simp [hi,hil]
      · simp [hi]
    simp_rw [he]
    rw [clock_prefix_sum,h0,sub_zero]

end HexagonPaper
