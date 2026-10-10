module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section

/-! An eventual genuine power bound extends to every positive system size
by an explicit finite sum. No uniform bound on the omitted sizes is assumed. -/
noncomputable section
open Filter
namespace FourPapersCommon
set_option maxHeartbeats 600000

theorem exists_global_nat_power_bound_of_eventually (f : ℕ → ℝ) (r C0 : ℝ)
    (h : ∀ᶠn : ℕ in atTop,f n ≤ C0*(n:ℝ)^r) :
    ∃C : ℝ,0<C ∧ ∀n : ℕ,0<n → f n ≤ C*(n:ℝ)^r := by
  obtain ⟨N0,hN0⟩:=eventually_atTop.mp h
  let K:=∑i∈Finset.range N0,|f i|/(i:ℝ)^r
  have hK : 0 ≤ K:=Finset.sum_nonneg (fun i _=>div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg i) _))
  let C:=|C0|+K+1
  have hC : 0<C:=by dsimp only [C];linarith [abs_nonneg C0]
  have hC0 : C0 ≤ C:=by dsimp only [C];linarith [le_abs_self C0]
  have hKC : K ≤ C:=by dsimp only [C];linarith [abs_nonneg C0]
  refine ⟨C,hC,?_⟩
  intro n hn
  have hp : 0<(n:ℝ)^r:=Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  by_cases hlarge : N0 ≤ n
  · exact (hN0 n hlarge).trans (mul_le_mul_of_nonneg_right hC0 hp.le)
  · have hnmem : n∈Finset.range N0:=Finset.mem_range.mpr (lt_of_not_ge hlarge)
    have hterm : |f n|/(n:ℝ)^r ≤ K:=Finset.single_le_sum
      (fun i _=>div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg i) _)) hnmem
    have hh:=mul_le_mul_of_nonneg_right hterm hp.le
    rw [div_mul_cancel₀ _ hp.ne'] at hh
    exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_right hKC hp.le))

end FourPapersCommon
