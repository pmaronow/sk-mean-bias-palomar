module
public import QuantitativePaper.VectorNodeGradient
public import QuantitativePaper.VectorTailTimeBounds

@[expose] public section

/-! The true variance budget of a remaining finite recursion is at most the
total physical variance, independently of its number of levels. -/
noncomputable section
open Set
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1100000

theorem abs_vectorRecursion_sub_terminal_uniform {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (j : ℕ)
    (hj : j ≤ k+2) (x : Field n) :
    |vectorRecursion s β t p j x-vectorTerminalPotential n β t p x| ≤
      (n:ℝ)*((1-t)*β^2)/2 := by
  have hi : k+2-j ≤ k+2 := Nat.sub_le _ _
  have hq : s.q (k+2-j) ∈ Icc (0:ℝ) 1 := ⟨s.q_nonneg hi,s.q_le_one hi⟩
  have hh := vectorTailRecursion_time_abs_sub_le s β t (s.q (k+2-j)) 1 ht
    hq ⟨zero_le_one,le_rfl⟩ p x
  rw [vectorTailRecursion_at_node s β t (k+2-j) hi p,
    show k+2-(k+2-j)=j by omega,vectorTailRecursion_one s β t p le_rfl] at hh
  have hc : 0 ≤ (n:ℝ)*((1-t)*β^2)/2 := by positivity
  have hlen : |s.q (k+2-j)-1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hq.2)]
    linarith [hq.1]
  exact hh.trans (mul_le_of_le_one_right hc hlen)

theorem abs_vectorRecursion_sub_initial_terminal_uniform {n k : ℕ}
    (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ)
    (j : ℕ) (hj : j ≤ k+2) (x y : Field n) :
    |vectorRecursion s β t p j y-vectorTerminalPotential n β t p x| ≤
      (n:ℝ)*((1-t)*β^2)/2+Real.sqrt (n:ℝ)*‖y-x‖ := by
  have hterm := (vectorTerminalPotential_lipschitz n β t p).norm_sub_le y x
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _),Real.norm_eq_abs] at hterm
  exact (abs_sub_le _ _ _).trans (add_le_add
    (abs_vectorRecursion_sub_terminal_uniform s β t ht p j hj y) hterm)

end QuantitativePaper
