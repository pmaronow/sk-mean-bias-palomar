module
public import QuantitativeFollowup.FourTermBudgetAbsorption

@[expose] public section

/-! Exact exponents of the four-term budget at the printed tilt N^(-7/50).
These are arithmetic identities, independent of the remaining stable-interval
model estimate. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 600000

theorem fourTermBudget_optimal_tilt_range (N : ℝ) (hN : 1 ≤ N) :
    N^(-(7/50:ℝ)) ∈ Icc N⁻¹ 1 ∧ 0 < N^(-(7/50:ℝ)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  refine ⟨⟨?_, Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)⟩,
    Real.rpow_pos_of_pos hNp _⟩
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

theorem fourTermBudget_optimal_trial_power (N : ℝ) (hN : 0 ≤ N) :
    (N^(-(7/50:ℝ)))^5 = N^(-(7/10:ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
  norm_num

theorem fourTermBudget_optimal_first_power (N : ℝ) (hN : 0 < N) :
    N^(-(2/3:ℝ))*(N^(-(7/50:ℝ)))^(5/21:ℝ) = N^(-(7/10:ℝ)) := by
  rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  norm_num

theorem fourTermBudget_optimal_second_power (N : ℝ) (hN : 0 < N) :
    N^(-(7/9:ℝ))*(N^(-(7/50:ℝ)))^(-(7/18:ℝ)) = N^(-(217/300:ℝ)) := by
  rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  norm_num

theorem fourTermBudget_optimal_log_power (N : ℝ) (hN : 0 < N) :
    (Real.log (2+N))^3/(N*(N^(-(7/50:ℝ)))^(12/7:ℝ)) =
      (Real.log (2+N))^3*N^(-(19/25:ℝ)) := by
  rw [← Real.rpow_mul hN.le]
  conv_lhs => arg 2; arg 1; rw [← Real.rpow_one N]
  rw [← Real.rpow_add hN]
  norm_num
  rw [div_eq_mul_inv, ← Real.rpow_neg hN.le]

theorem fourTermBudgetRate_optimal (N : ℝ) (hN : 0 < N) :
    fourTermBudgetRate N (N^(-(7/50:ℝ))) =
      2*N^(-(7/10:ℝ)) + N^(-(217/300:ℝ)) +
        (Real.log (2+N))^3*N^(-(19/25:ℝ)) := by
  rw [fourTermBudgetRate, fourTermBudget_optimal_first_power N hN,
    fourTermBudget_optimal_second_power N hN, fourTermBudget_optimal_log_power N hN]
  ring

end QuantitativeFollowup
