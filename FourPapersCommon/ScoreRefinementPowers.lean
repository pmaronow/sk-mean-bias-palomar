module
public import FourPapersCommon.TruncatedPowerIntegrals
public import FourPapersCommon.RefinedShellPowers
public import QuantitativeFollowup.DyadicLogOptimization

@[expose] public section

/-! Elementary scalar integrals and logarithmic powers for the literal spin-score refinement. -/
noncomputable section
open Set MeasureTheory intervalIntegral QuantitativeFollowup
namespace FourPapersCommon
set_option maxHeartbeats 1800000

theorem min_one_reciprocal_le_three_quarters (b x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    min 1 (b/x) ≤ b^(3/4 : ℝ)*x^(-(3/4 : ℝ)) := by
  have hz : 0 < b/x := div_pos hb hx
  have he : (b/x)^(3/4 : ℝ) = b^(3/4 : ℝ)*x^(-(3/4 : ℝ)) := by
    rw [Real.div_rpow hb.le hx.le, Real.rpow_neg hx.le]
    ring
  rw [← he]
  by_cases h : b/x ≤ 1
  · exact (min_le_right _ _).trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hz h
        (by norm_num : (3/4 : ℝ) ≤ 1))
  · exact (min_le_left _ _).trans (Real.one_le_rpow (le_of_not_ge h) (by norm_num))

theorem integral_score_reciprocal_window (ε m : ℝ) (hε : 0 < ε) (hm : 0 < m) :
    IntegrableOn (fun x : ℝ => min 1 (2*ε/x)) (Ioo 0 m) ∧
      (∫ x in Ioo (0 : ℝ) m, min 1 (2*ε/x)) ≤ 8*ε^(3/4 : ℝ)*m^(1/4 : ℝ) := by
  have hi := integrableOn_truncated_reciprocal 1 (2*ε) m (by norm_num) (by positivity)
  have hip : IntervalIntegrable (fun x : ℝ => x^(-(3/4 : ℝ))) volume 0 m :=
    intervalIntegrable_rpow' (by norm_num)
  have his := (intervalIntegrable_iff_integrableOn_Ioo_of_le hm.le).mp hip
  have he : (∫ x in Ioo (0 : ℝ) m, x^(-(3/4 : ℝ))) = 4*m^(1/4 : ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hm.le,
      integral_rpow (Or.inl (by norm_num : -1 < -(3/4 : ℝ)))]
    norm_num
    ring
  have h := setIntegral_mono_on hi (his.const_mul ((2*ε)^(3/4 : ℝ))) measurableSet_Ioo
    (fun x hx => min_one_reciprocal_le_three_quarters (2*ε) x (by positivity) hx.1)
  rw [MeasureTheory.integral_const_mul, he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le] at h
  have htwo : (2 : ℝ)^(3/4 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (3/4 : ℝ) ≤ 1)
  refine ⟨hi, h.trans ?_⟩
  have hp := mul_nonneg (Real.rpow_nonneg hε.le (3/4 : ℝ)) (Real.rpow_nonneg hm.le (1/4 : ℝ))
  nlinarith

theorem score_logPlus_square_le_quarter_power (X : ℝ) (hX : 1 ≤ X) :
    (1+logPlus X)^2 ≤ 64*X^(1/4 : ℝ) := by
  have hx : 0 < X := zero_lt_one.trans_le hX
  have hy : 0 < X^(1/8 : ℝ) := Real.rpow_pos_of_pos hx _
  have hlog := Real.log_le_sub_one_of_pos hy
  rw [Real.log_rpow hx] at hlog
  have hln : 0 ≤ Real.log X := Real.log_nonneg hX
  have hmax : logPlus X = Real.log X := max_eq_left hln
  have hbd : 1+logPlus X ≤ 8*X^(1/8 : ℝ) := by rw [hmax]; linarith
  have hsq := pow_le_pow_left₀ (by rw [hmax]; linarith) hbd 2
  have he : (X^(1/8 : ℝ))^2 = X^(1/4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  nlinarith

theorem score_logarithmic_residual_shell (M u m : ℝ) (hM : 0 < M) (hu : 0 < u)
    (hm : 0 ≤ m) (hmu : m ≤ u) (hMu : 1 ≤ M*u^2) :
    112*m*(1+logPlus (M*u^2))^2/(M*u^2) ≤
      7168*M^(-(3/4 : ℝ))*u^(-(1/2 : ℝ)) := by
  have hx : 0 < M*u^2 := mul_pos hM (sq_pos_of_pos hu)
  have hlog := score_logPlus_square_le_quarter_power (M*u^2) hMu
  have he : (M*u^2)^(1/4 : ℝ)/(M*u^2) = (M*u^2)^(-(3/4 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hx]
    norm_num
  have hp : u*(M*u^2)^(-(3/4 : ℝ)) = M^(-(3/4 : ℝ))*u^(-(1/2 : ℝ)) := by
    have huP : (u^2)^(-(3/4 : ℝ)) = u^((2 : ℝ)*(-(3/4 : ℝ))) := by
      rw [Real.rpow_mul hu.le, Real.rpow_two]
    rw [Real.mul_rpow hM.le (sq_nonneg u), huP]
    calc
      _ = M^(-(3/4 : ℝ))*(u^(1 : ℝ)*u^((2 : ℝ)*(-(3/4 : ℝ)))) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hu]; norm_num
  calc
    _ ≤ 112*m*(64*(M*u^2)^(1/4 : ℝ))/(M*u^2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) hx.le
    _ = 7168*m*(M*u^2)^(-(3/4 : ℝ)) := by rw [← he]; ring
    _ ≤ 7168*u*(M*u^2)^(-(3/4 : ℝ)) := by gcongr
    _ = _ := by rw [mul_assoc, hp]; ring

end FourPapersCommon
