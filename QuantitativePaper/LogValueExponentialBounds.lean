module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! Actual two-sided exponential bounds give linear growth of a logarithm. -/
noncomputable section
namespace QuantitativePaper

theorem abs_log_le_of_exponential_bounds (z C R d D x : ℝ)
    (hC : 0 < C) (hd : 0 < d) (hR : 0 ≤ R) (hD : 0 ≤ D) (hx : 0 ≤ x)
    (hlo : d*Real.exp (-D*x) ≤ z) (hhi : z ≤ C*Real.exp (R*x)) :
    |Real.log z| ≤ (|Real.log C|+|Real.log d|)+(R+D)*x := by
  have hz : 0 < z := (mul_pos hd (Real.exp_pos _)).trans_le hlo
  have hl := Real.log_le_log (mul_pos hd (Real.exp_pos _)) hlo
  have hu := Real.log_le_log hz hhi
  rw [Real.log_mul hd.ne' (Real.exp_ne_zero _),Real.log_exp] at hl
  rw [Real.log_mul hC.ne' (Real.exp_ne_zero _),Real.log_exp] at hu
  rw [abs_le]
  constructor <;> nlinarith [le_abs_self (Real.log C),neg_abs_le (Real.log d),
    abs_nonneg (Real.log C),abs_nonneg (Real.log d)]

end QuantitativePaper
