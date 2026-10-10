module
public import HexagonPaper.Main
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! The rigorous little-o assertion in the physics discussion. -/
noncomputable section
open Filter QuantitativeFollowup
open scoped Topology
namespace HexagonPaper

theorem mean_bias_little_o_two_thirds (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (2 / 3 : ℝ) * finiteBias N β)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := main_mean_bias β hβ
  have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 30 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 30)).comp
        tendsto_natCast_atTop_atTop).const_mul C
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hbound N hN).1
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have h := mul_le_mul_of_nonneg_left (hbound N hN).2
      (Real.rpow_nonneg hNp.le (2 / 3 : ℝ))
    have hp : (N : ℝ) ^ (2 / 3 : ℝ) * (C * (N : ℝ) ^ (-(7 / 10 : ℝ))) =
        C * (N : ℝ) ^ (-(1 / 30 : ℝ)) := by
      rw [← mul_assoc, mul_comm ((N : ℝ) ^ (2 / 3 : ℝ)) C, mul_assoc,
        ← Real.rpow_add hNp]
      congr 1
      norm_num
    simpa only [hp] using h

end HexagonPaper
