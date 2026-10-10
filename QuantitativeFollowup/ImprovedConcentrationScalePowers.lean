module
public import QuantitativeFollowup.ImprovedWindowScalePowers

@[expose] public section

/-! Exact real-power arithmetic for the improved centered variance scale. -/
noncomputable section
namespace QuantitativeFollowup
set_option maxHeartbeats 900000

theorem improved_optimal_centered_secant_scale (N : ℝ) (hN : 0<N) :
    N*(N^(-(7/50:ℝ)))^4=N^(11/25:ℝ) := by
  rw [←Real.rpow_mul_natCast hN.le]
  calc
    _=N^(1:ℝ)*N^((-(7/50:ℝ))*(4:ℕ)):=by rw [Real.rpow_one]
    _=_:=by rw [←Real.rpow_add hN];congr 1 <;> norm_num

theorem improved_optimal_mean_power (N : ℝ) (hN : 0<N) :
    N^(-(7/10:ℝ))=(N^(-(7/50:ℝ)))^5 := by
  rw [←Real.rpow_mul_natCast hN.le]
  norm_num

end QuantitativeFollowup
