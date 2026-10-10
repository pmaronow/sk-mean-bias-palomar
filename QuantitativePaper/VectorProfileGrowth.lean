module
public import QuantitativePaper.VectorProfileRecursion
public import QuantitativePaper.VectorVarianceBounds

@[expose] public section

/-! Genuine uniform value growth of every physical affine-profile recursion.
The bound follows from the actual Gaussian variance derivative, independently
of profile masses and the number of coincident grid levels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorRecursion_sub_terminal_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    0 ≤ vectorRecursion s β t p j x-vectorTerminalPotential n β t p x ∧
      vectorRecursion s β t p j x-vectorTerminalPotential n β t p x ≤
        (j:ℝ)*(n:ℝ)/2*((1-t)*β^2) := by
  induction j with
  | zero => simp [vectorRecursion]
  | succ j ih =>
    let c := (1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    have hq : s.q (k+1-j) ≤ s.q (k+2-j) :=
      s.q_mono' _ (Nat.sub_le _ _) _ (by omega)
    have hc : 0 ≤ c := mul_nonneg (sub_nonneg.mpr ht)
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hq))
    have hc' : c ≤ (1-t)*β^2 := by
      dsimp only [c]
      have hdiff : s.q (k+2-j)-s.q (k+1-j) ≤ 1 := by
        linarith [s.q_le_one (Nat.sub_le (k+2) j), s.q_nonneg (by omega : k+1-j ≤ k+2)]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiff (sq_nonneg β))
        (sub_nonneg.mpr ht)
    have hb := vectorColeHopfStep_recursion_variance_sub_bounds s β t p j (s.m (k+1-j))
      ⟨s.m_nonneg (Nat.sub_le _ _), s.m_le_one (Nat.sub_le _ _)⟩
      0 c (by norm_num) hc x
    rw [vectorColeHopfStep_zero_variance] at hb
    rw [vectorRecursion]
    change 0 ≤ vectorColeHopfStep c (s.m (k+1-j)) (vectorRecursion s β t p j) x -
      vectorTerminalPotential n β t p x ∧
      vectorColeHopfStep c (s.m (k+1-j)) (vectorRecursion s β t p j) x -
        vectorTerminalPotential n β t p x ≤ _
    have hbudget := mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ (n:ℝ)/2)
    constructor
    · linarith [ih.1, hb.1]
    · simp only [Nat.cast_add, Nat.cast_one]
      have hstep := hb.2.trans (by simpa only [sub_zero] using hbudget)
      nlinarith [ih.2, hstep]

theorem vectorProfileRecursion_abs_le {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1)
    (j : ℕ) (p : VectorParameter n) :
    |vectorProfileRecursion s₀ s₁ β t θ p.1 j p.2| ≤
      |vectorTerminalPotential n β t (0 : Couplings n×ℝ) (0 : Field n)| +
        (j:ℝ)*(n:ℝ)/2*((1-t)*β^2) +
        (vectorJointLipschitzConstant n β t:ℝ)*‖p‖ := by
  let s := vectorProfileScheme s₀ s₁ θ hθ
  rw [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ]
  have hzero := vectorRecursion_sub_terminal_bounds s β t ht (0 : Couplings n×ℝ) j (0 : Field n)
  have hl := (vectorRecursion_joint_lipschitz (n:=n) s β t j).dist_le_mul p 0
  rw [Real.dist_eq, dist_zero_right] at hl
  change |vectorRecursion s β t p.1 j p.2-vectorRecursion (n:=n) s β t 0 j 0| ≤ _ at hl
  have h0 : |vectorRecursion (n:=n) s β t 0 j 0| ≤
      |vectorTerminalPotential n β t 0 0|+(j:ℝ)*(n:ℝ)/2*((1-t)*β^2) := by
    have hbudget0 : 0 ≤ (j:ℝ)*(n:ℝ)/2*((1-t)*β^2) := by positivity
    exact (abs_le.mpr ⟨by linarith [neg_abs_le (vectorTerminalPotential n β t 0 0), hzero.1],
      by linarith [le_abs_self (vectorTerminalPotential n β t 0 0), hzero.2]⟩)
  have hh := abs_add_le (vectorRecursion (n:=n) s β t 0 j 0)
    (vectorRecursion s β t p.1 j p.2-vectorRecursion (n:=n) s β t 0 j 0)
  rw [add_sub_cancel] at hh
  exact hh.trans (by linarith)

end QuantitativePaper
