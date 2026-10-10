module
public import QuantitativeFollowup.FourTermBudgetOptimalPowers

@[expose] public section

/-! Genuine real-power arithmetic for the printed large-tilt window.
No error estimate or fluctuation statement is asserted here. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem fourTermBudget_window_monomial (N A lam a b : ℝ) (hN : 0 < N)
    (hA : 0 < A) (hb : 0 ≤ b) (hwin : A*N^(-(7/50:ℝ)) ≤ lam) :
    N^a*lam^(-b) ≤ A^(-b)*N^(a+(7/50:ℝ)*b) := by
  have hh := Real.rpow_le_rpow_of_nonpos
    (mul_pos hA (Real.rpow_pos_of_pos hN _)) hwin (neg_nonpos.mpr hb)
  calc
    _ ≤ N^a*(A*N^(-(7/50:ℝ)))^(-b) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [Real.mul_rpow hA.le (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le]
      calc
        _ = A^(-b)*(N^a*N^((-(7/50:ℝ))*(-b))) := by ring
        _ = _ := by rw [← Real.rpow_add hN]; congr 2 <;> ring

theorem fourTermBudget_rate_div_trial (N lam : ℝ) (hN : 0 < N) (hlam : 0 < lam) :
    fourTermBudgetRate N lam/lam^5 =
      N^(-(7/10:ℝ))*lam^(-5:ℝ) +
      N^(-(2/3:ℝ))*lam^(-(100/21:ℝ)) +
      N^(-(7/9:ℝ))*lam^(-(97/18:ℝ)) +
      (Real.log (2+N))^3*N^(-1:ℝ)*lam^(-(47/7:ℝ)) := by
  have hfirst : (lam^5)⁻¹ = lam^(-5:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hlam.le]
    norm_num
  rw [div_eq_mul_inv, hfirst, fourTermBudgetRate]
  have h1 : lam^(5/21:ℝ)*lam^(-5:ℝ) = lam^(-(100/21:ℝ)) := by
    rw [← Real.rpow_add hlam]; norm_num
  have h2 : lam^(-(7/18:ℝ))*lam^(-5:ℝ) = lam^(-(97/18:ℝ)) := by
    rw [← Real.rpow_add hlam]; norm_num
  have h3 : lam^(-(12/7:ℝ))*lam^(-5:ℝ) = lam^(-(47/7:ℝ)) := by
    rw [← Real.rpow_add hlam]; norm_num
  have hden : (Real.log (2+N))^3/(N*lam^(12/7:ℝ)) =
      (Real.log (2+N))^3*N^(-1:ℝ)*lam^(-(12/7:ℝ)) := by
    change (Real.log (2+N))^3*(N*lam^(12/7:ℝ))⁻¹ = _
    rw [mul_inv_rev, ← Real.rpow_neg hlam.le, ← Real.rpow_neg_one N]
    ring
  rw [hden]
  calc
    _ = N^(-(7/10:ℝ))*lam^(-5:ℝ) +
        N^(-(2/3:ℝ))*(lam^(5/21:ℝ)*lam^(-5:ℝ)) +
        N^(-(7/9:ℝ))*(lam^(-(7/18:ℝ))*lam^(-5:ℝ)) +
        (Real.log (2+N))^3*N^(-1:ℝ)*(lam^(-(12/7:ℝ))*lam^(-5:ℝ)) := by ring
    _ = _ := by rw [h1, h2, h3]

theorem fourTermBudget_window_quotient (N A lam : ℝ) (hN : 2 ≤ N)
    (hA : 1 ≤ A) (hwin : A*N^(-(7/50:ℝ)) ≤ lam) :
    fourTermBudgetRate N lam/lam^5 ≤
      A^(-5:ℝ) + A^(-(100/21:ℝ)) + N^(-(7/300:ℝ)) +
        N^(-(3/50:ℝ))*(Real.log (2+N))^3 := by
  have hNp : 0 < N := by linarith
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hlp : 0 < lam := (mul_pos hAp (Real.rpow_pos_of_pos hNp _)).trans_le hwin
  rw [fourTermBudget_rate_div_trial N lam hNp hlp]
  have h0 := fourTermBudget_window_monomial N A lam (-(7/10:ℝ)) 5 hNp hAp (by norm_num) hwin
  have h1 := fourTermBudget_window_monomial N A lam (-(2/3:ℝ)) (100/21:ℝ) hNp hAp (by norm_num) hwin
  have h2 := fourTermBudget_window_monomial N A lam (-(7/9:ℝ)) (97/18:ℝ) hNp hAp (by norm_num) hwin
  have h3 := fourTermBudget_window_monomial N A lam (-1:ℝ) (47/7:ℝ) hNp hAp (by norm_num) hwin
  norm_num only [show -(7/10:ℝ)+(7/50:ℝ)*5 = 0 by norm_num,
    Real.rpow_zero, mul_one] at h0
  norm_num only [show -(2/3:ℝ)+(7/50:ℝ)*(100/21:ℝ) = 0 by norm_num,
    Real.rpow_zero, mul_one] at h1
  norm_num at h2 h3
  have hA2 := Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num : -(97/18:ℝ) ≤ 0)
  have hA3 := Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num : -(47/7:ℝ) ≤ 0)
  have h2' : N^(-(7/9:ℝ))*lam^(-(97/18:ℝ)) ≤ N^(-(7/300:ℝ)) :=
    h2.trans ((mul_le_mul_of_nonneg_right hA2 (Real.rpow_nonneg hNp.le _)).trans_eq (one_mul _))
  have h3' : N^(-1:ℝ)*lam^(-(47/7:ℝ)) ≤ N^(-(3/50:ℝ)) :=
    h3.trans ((mul_le_mul_of_nonneg_right hA3 (Real.rpow_nonneg hNp.le _)).trans_eq (one_mul _))
  have hlog : 0 ≤ (Real.log (2+N))^3 := pow_nonneg
    (Real.log_nonneg (by linarith)) _
  have h3'' := mul_le_mul_of_nonneg_left h3' hlog
  calc
    _ ≤ A^(-5:ℝ) + A^(-(100/21:ℝ)) + N^(-(7/300:ℝ)) +
        (Real.log (2+N))^3*N^(-(3/50:ℝ)) := by nlinarith
    _ = _ := by ring

theorem fourTermBudget_error_window (N A lam e C : ℝ) (hN : 2 ≤ N)
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hwin : A*N^(-(7/50:ℝ)) ≤ lam)
    (hbound : e ≤ C*fourTermBudgetRate N lam) :
    e/lam^5 ≤ C*(A^(-5:ℝ) + A^(-(100/21:ℝ)) + N^(-(7/300:ℝ)) +
      N^(-(3/50:ℝ))*(Real.log (2+N))^3) := by
  have hNp : 0 < N := by linarith
  have hlp : 0 < lam := (mul_pos (zero_lt_one.trans_le hA)
    (Real.rpow_pos_of_pos hNp _)).trans_le hwin
  calc
    _ ≤ C*fourTermBudgetRate N lam/lam^5 :=
      div_le_div_of_nonneg_right hbound (pow_nonneg hlp.le _)
    _ = C*(fourTermBudgetRate N lam/lam^5) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (fourTermBudget_window_quotient N A lam hN hA hwin) hC

theorem fourTermBudget_window_quadratic_correction (N A lam : ℝ) (hN : 0 < N)
    (hA : 0 < A) (hwin : A*N^(-(7/50:ℝ)) ≤ lam) :
    lam^2/(4*N*lam^6) ≤ A^(-4:ℝ)*N^(-(11/25:ℝ))/4 := by
  have hlp : 0 < lam := (mul_pos hA (Real.rpow_pos_of_pos hN _)).trans_le hwin
  have hh := fourTermBudget_window_monomial N A lam (-1:ℝ) 4 hN hA (by norm_num) hwin
  norm_num only [show (-1:ℝ)+(7/50:ℝ)*4 = -(11/25:ℝ) by norm_num] at hh
  have heq : lam^2/(4*N*lam^6) = (N^(-1:ℝ)*lam^(-4:ℝ))/4 := by
    norm_num only [Real.rpow_neg_one, Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right hh (by norm_num)

end QuantitativeFollowup
