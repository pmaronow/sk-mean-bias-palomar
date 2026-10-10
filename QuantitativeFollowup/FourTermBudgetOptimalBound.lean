module
public import QuantitativeFollowup.FourTermBudgetOptimalPowers

@[expose] public section

/-! A uniform numerical bound at the actual optimal tilt. This leaf
contains no model-error hypothesis or finite-size conclusion. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

theorem fourTermBudget_log_cube_bound (N : ℝ) (hN : 2 ≤ N) :
    (Real.log (2+N))^3 ≤ (Real.log 2+50)^3*N^(3/50:ℝ) := by
  have hNp : 0<N:=by linarith
  have hN1 : 1 ≤ N:=by linarith
  have hp : 1 ≤ N^(1/50:ℝ):=Real.one_le_rpow hN1 (by norm_num)
  have hlog2 : 0 ≤ Real.log 2:=Real.log_nonneg (by norm_num)
  have hlog : 0 ≤ Real.log (2+N):=Real.log_nonneg (by linarith)
  have hl : Real.log (2+N) ≤ (Real.log 2+50)*N^(1/50:ℝ):=by
    have hh:=Real.log_le_log (by linarith : (0:ℝ)<2+N) (by linarith : 2+N ≤ 2*N)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hNp.ne'] at hh
    have hr:=Real.log_le_rpow_div hNp.le (by norm_num : (0:ℝ)<1/50)
    have hconst:=mul_le_mul_of_nonneg_left hp hlog2
    norm_num only [div_div,div_one] at hr
    nlinarith
  have hc:=pow_le_pow_left₀ hlog hl 3
  rw [mul_pow] at hc
  have he : (N^(1/50:ℝ))^3=N^(3/50:ℝ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
    norm_num
  rwa [he] at hc

theorem fourTermBudgetRate_optimal_bound (N : ℝ) (hN : 2 ≤ N) :
    fourTermBudgetRate N (N^(-(7/50:ℝ))) ≤
      (3+(Real.log 2+50)^3)*N^(-(7/10:ℝ)) := by
  have hNp : 0<N:=by linarith
  rw [fourTermBudgetRate_optimal N hNp]
  have hsecond : N^(-(217/300:ℝ)) ≤ N^(-(7/10:ℝ)):=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by norm_num)
  have hlog:=mul_le_mul_of_nonneg_right (fourTermBudget_log_cube_bound N hN)
    (Real.rpow_nonneg hNp.le (-(19/25:ℝ)))
  have hp : N^(3/50:ℝ)*N^(-(19/25:ℝ))=N^(-(7/10:ℝ)):=by
    rw [←Real.rpow_add hNp]
    norm_num
  rw [mul_assoc,hp] at hlog
  nlinarith only [hsecond,hlog]

end QuantitativeFollowup
