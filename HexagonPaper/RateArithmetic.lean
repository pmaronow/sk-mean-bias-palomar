module
public import QuantitativeFollowup.RateOptimization

@[expose] public section

/-! Literal exponent identities in the revised final proof and exponent
remark. These numerical statements do not assume an SK bias conclusion. -/

noncomputable section
namespace HexagonPaper
open QuantitativeFollowup

theorem critical_exponent_balance (a : ℝ) :
    a = (2 / 3 : ℝ) + a / 21 ↔ a = (7 / 10 : ℝ) := by
  constructor <;> intro h <;> linarith

theorem normalized_critical_budget {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) :
    N ^ (-(2 / 3 : ℝ)) *
      (N ^ (-(7 / 10 : ℝ)) * x) ^ (1 / 21 : ℝ) =
        N ^ (-(7 / 10 : ℝ)) * x ^ (1 / 21 : ℝ) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) hx,
    ← Real.rpow_mul hN.le, ← mul_assoc, ← Real.rpow_add hN]
  congr 1
  norm_num

theorem normalized_localization_budget {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) :
    N ^ (-(2 / 3 : ℝ)) * (followupScale N) ^ (-(1 / 3 : ℝ)) *
      (N ^ (-(7 / 10 : ℝ)) * x) ^ (1 / 7 : ℝ) =
        N ^ (-(7 / 10 : ℝ)) * N ^ (-(1 / 50 : ℝ)) * x ^ (1 / 7 : ℝ) := by
  unfold followupScale
  rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) hx,
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le,
    ← mul_assoc, ← Real.rpow_add hN, ← Real.rpow_add hN,
    ← Real.rpow_add hN]
  congr 1
  norm_num

theorem normalized_stable_interval {N : ℝ} (hN : 0 < N) :
    N ^ (-(19 / 25 : ℝ)) / N ^ (-(7 / 10 : ℝ)) =
      N ^ (-(3 / 50 : ℝ)) := by
  rw [← Real.rpow_sub hN]
  congr 1
  norm_num

theorem elementary_error_below_stable_interval {N : ℝ} (hN : 1 ≤ N) :
    N⁻¹ * (followupScale N)⁻¹ ≤ N ^ (-(19 / 25 : ℝ)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have h : N⁻¹ * (followupScale N)⁻¹ = N ^ (-(43 / 50 : ℝ)) := by
    rw [← Real.rpow_neg_one, followupScale, ← Real.rpow_neg_one,
      ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp]
    congr 1
    norm_num
  rw [h]
  exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

theorem normalized_log_cube_bounded {N : ℝ} (hN : 2 ≤ N) :
    N ^ (-(3 / 50 : ℝ)) * (Real.log (2 + N)) ^ 3 ≤
      (Real.log 2 + 50) ^ 3 := by
  have hNp : 0 < N := by linarith
  have h := mul_le_mul_of_nonneg_left (followup_log_cube_bound hN)
    (Real.rpow_nonneg hNp.le (-(3 / 50 : ℝ)))
  have he : N ^ (-(3 / 50 : ℝ)) *
      ((Real.log 2 + 50) ^ 3 * N ^ (3 / 50 : ℝ)) =
        (Real.log 2 + 50) ^ 3 := by
    calc
      _ = (Real.log 2 + 50) ^ 3 *
          (N ^ (-(3 / 50 : ℝ)) * N ^ (3 / 50 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  simpa only [he] using h

end HexagonPaper
