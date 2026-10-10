module
public import QuantitativePaper.ExponentialJetProducts

@[expose] public section

/-! Actual linear value growth and positive-order jet envelopes combine into
a single envelope. Multiplication by a bounded smooth parameter factor then
preserves exponential positive-order growth. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1400000

theorem exists_all_order_power_envelope (N : ℕ) (f : E → ℝ) (U : Set E)
    (B L K D : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hK : 1 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, |f x| ≤ B+L*‖x‖)
    (hjets : ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (K*Real.exp (D*‖x‖))^j) :
    ∃ C R : ℝ, 1 ≤ C ∧ 1 ≤ R ∧ ∀ j, j ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (C*Real.exp (R*‖x‖))^(j+1) := by
  let C := max K (B+L)
  let R := max 1 D
  have hC : 1 ≤ C := hK.trans (le_max_left _ _)
  have hR : 1 ≤ R := le_max_left _ _
  refine ⟨C, R, hC, hR, ?_⟩
  intro j hj x hx
  have he : Real.exp (D*‖x‖) ≤ Real.exp (R*‖x‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hP : 1 ≤ C*Real.exp (R*‖x‖) := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_exp_iff.mpr (mul_nonneg (zero_le_one.trans hR) (norm_nonneg _)))
  by_cases hj0 : j=0
  · subst j
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, zero_add, pow_one]
    apply (hvalue x hx).trans ((linear_growth_le_exponential B L ‖x‖ hB hL (norm_nonneg _)).trans ?_)
    exact mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg x, hR])) (Real.exp_pos _).le
      (zero_le_one.trans hC)
  · apply (hjets j (by omega) hj x hx).trans
    have hh : K*Real.exp (D*‖x‖) ≤ C*Real.exp (R*‖x‖) :=
      mul_le_mul (le_max_left _ _) he (Real.exp_pos _).le (zero_le_one.trans hC)
    exact (pow_le_pow_left₀ (by positivity) hh j).trans
      (pow_le_pow_right₀ hP (Nat.le_succ j))

theorem mul_smooth_exp_jets_on_open (N : ℕ) (f g : E → ℝ) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ N f U) (hg : ContDiffOn ℝ N g U)
    (B L K D M : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hK : 1 ≤ K) (hD : 0 ≤ D) (hM : 1 ≤ M)
    (hvalue : ∀ x ∈ U, |f x| ≤ B+L*‖x‖)
    (hjets : ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (K*Real.exp (D*‖x‖))^j)
    (hgjets : ∀ j, j ≤ N → ∀ x ∈ U, ‖iteratedFDeriv ℝ j g x‖ ≤ M) :
    ContDiffOn ℝ N (fun x => g x*f x) U ∧
      ∃ C R : ℝ, 1 ≤ C ∧ 1 ≤ R ∧ ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U,
        ‖iteratedFDeriv ℝ j (fun x => g x*f x) x‖ ≤ (C*Real.exp (R*‖x‖))^j := by
  obtain ⟨C, R, hC, hR, henv⟩ := exists_all_order_power_envelope N f U B L K D hB hL hK hD hvalue hjets
  refine ⟨hg.mul hf, 2*M*C^2, 2*R, ?_, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hM) (one_le_pow₀ hC)
  · linarith
  · intro j hj0 hj x hx
    have hP : 1 ≤ C*Real.exp (R*‖x‖) := one_le_mul_of_one_le_of_one_le hC
      (Real.one_le_exp_iff.mpr (mul_nonneg (zero_le_one.trans hR) (norm_nonneg _)))
    have hh := norm_iteratedFDeriv_mul_le_of_power_envelope f g U hU hf hg hj0 hj x hx M
      (C*Real.exp (R*‖x‖)) hM hP
      (fun i hi => henv i (hi.trans hj) x hx) (fun i hi => hgjets i (hi.trans hj) x hx)
    calc
      _ ≤ (2*M*(C*Real.exp (R*‖x‖))^2)^j := hh
      _ = (2*M*C^2*Real.exp ((2*R)*‖x‖))^j := by
        congr 1
        have heE : Real.exp (R*‖x‖)^2 = Real.exp ((2*R)*‖x‖) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [mul_pow, heE]
        ring


end QuantitativePaper
