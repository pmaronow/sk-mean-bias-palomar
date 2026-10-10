module
public import HexagonPaper.RateArithmetic
public import QuantitativeFollowup.SupportingPrintedFiniteSizeChainsInput

@[expose] public section

/-! The revised critical-tilt input is obtained from the actual SK
trial and stable-interval estimates, with their hypotheses discharged
in the imported native comparison theorem. -/

noncomputable section
open Set Filter MeasureTheory QuantitativePaper QuantitativeFollowup
open scoped Topology
namespace HexagonPaper

theorem critical_trial_error_input (β : ℝ) (hβ : 1 < β) :
    ∃ C L : ℝ, ∃ N₁ : ℕ, 0 < C ∧ 1 ≤ L ∧ 2 ≤ N₁ ∧
      ∀ N : ℕ, N₁ ≤ N →
        let lam := followupScale (N : ℝ)
        let eta := energyComparisonError N β lam + L * lam ^ 5
        energyComparisonError N β lam ≤
          C * (N : ℝ) ^ (-(19 / 25 : ℝ)) * (Real.log (2 + (N : ℝ))) ^ 3 +
          C * (N : ℝ) ^ (-(2 / 3 : ℝ)) * eta ^ (1 / 21 : ℝ) +
          C * (N : ℝ) ^ (-(2 / 3 : ℝ)) * lam ^ (-(1 / 3 : ℝ)) *
            eta ^ (1 / 7 : ℝ) := by
  obtain ⟨C, L, lambda0, hC, hL, h0, _, hinput⟩ :=
    supportingPrintedFiniteSize_same_error_input β hβ
  have hsmall : ∀ᶠ N : ℕ in atTop, followupScale (N : ℝ) ≤ lambda0 := by
    simpa only [followupScale, neg_div, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 50)).comp
        tendsto_natCast_atTop_atTop).eventually_le_const h0.1
  obtain ⟨Nt, hNt⟩ := eventually_atTop.1 hsmall
  refine ⟨C, L, max 2 Nt, hC, hL, le_max_left _ _, ?_⟩
  intro N hN
  have hn : 2 ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlam : followupScale (N : ℝ) ∈ Icc ((N : ℝ)⁻¹) lambda0 :=
    ⟨inv_le_followupScale hN1, hNt N ((le_max_right _ _).trans hN)⟩
  have h := hinput N hn (followupScale (N : ℝ)) hlam
  have he : C * (Real.log (2 + (N : ℝ))) ^ 3 /
      ((N : ℝ) * (followupScale (N : ℝ)) ^ (12 / 7 : ℝ)) =
        C * (N : ℝ) ^ (-(19 / 25 : ℝ)) * (Real.log (2 + (N : ℝ))) ^ 3 := by
    rw [div_eq_mul_inv, mul_inv, ← Real.rpow_neg (followupScale_pos hNp).le]
    calc
      _ = C * (Real.log (2 + (N : ℝ))) ^ 3 *
          ((N : ℝ)⁻¹ * (followupScale (N : ℝ)) ^ (-(12 / 7 : ℝ))) := by ring
      _ = _ := by
        have hpow := followupScale_fourth_error hNp
        simp only [neg_div] at hpow
        rw [hpow]
        ring
  rw [he] at h
  exact h

end HexagonPaper
