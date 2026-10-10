module
public import QuantitativeFollowup.Absorption
public import QuantitativePaper.AbsoluteComparisonAbsorptionPowers

@[expose] public section

/-! Exact monomial powers in the actual comparison-budget absorption. -/
noncomputable section
open Set QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000

 theorem fourTermBudget_first_trial_power (N lam C L : ℝ) (hN : 0<N)
    (hlam : 0<lam) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    (C*N^(-(2/3:ℝ)))*(L*lam^5)^(1/21:ℝ)=
      (C*L^(1/21:ℝ))*N^(-(2/3:ℝ))*lam^(5/21:ℝ) := by
  rw [Real.mul_rpow hL (pow_nonneg hlam.le 5),←Real.rpow_natCast,
    ←Real.rpow_mul hlam.le]
  norm_num
  ring

 theorem fourTermBudget_first_young_power (N C : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) :
    (C*N^(-(2/3:ℝ)))^(21/20:ℝ)=C^(21/20:ℝ)*N^(-(7/10:ℝ)) := by
  rw [Real.mul_rpow hC (Real.rpow_nonneg hN _),←Real.rpow_mul hN]
  norm_num

 theorem fourTermBudget_second_trial_power (N lam C L : ℝ) (hN : 0<N)
    (hlam : 0<lam) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    (C*N^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))*(L*lam^5)^(1/7:ℝ)=
      (C*L^(1/7:ℝ))*N^(-(2/3:ℝ))*lam^(8/21:ℝ) := by
  rw [Real.mul_rpow hL (pow_nonneg hlam.le 5)]
  have he : (lam^5)^(1/7:ℝ)=lam^(5/7:ℝ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hlam.le]
    norm_num
  rw [he]
  calc
    _=(C*L^(1/7:ℝ))*N^(-(2/3:ℝ))*(lam^(-(1/3:ℝ))*lam^(5/7:ℝ)):=by ring
    _=_:=by rw [←Real.rpow_add hlam];norm_num

 theorem fourTermBudget_second_trial_le (N lam C L : ℝ) (hN : 0<N)
    (hlam : lam∈Ioc (0:ℝ) 1) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    (C*N^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))*(L*lam^5)^(1/7:ℝ) ≤ 
      (C*L^(1/7:ℝ))*N^(-(2/3:ℝ))*lam^(5/21:ℝ) := by
  rw [fourTermBudget_second_trial_power N lam C L hN hlam.1 hC hL]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hlam.1 hlam.2 (by norm_num : (5/21:ℝ) ≤ 8/21))
    (by positivity)

 theorem fourTermBudget_second_young_power (N lam C : ℝ) (hN : 0 ≤ N)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C) :
    (C*N^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))^(7/6:ℝ)=
      C^(7/6:ℝ)*N^(-(7/9:ℝ))*lam^(-(7/18:ℝ)) := by
  rw [Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hN _)) (Real.rpow_nonneg hlam _),
    Real.mul_rpow hC (Real.rpow_nonneg hN _),←Real.rpow_mul hN,←Real.rpow_mul hlam]
  norm_num

end QuantitativeFollowup
