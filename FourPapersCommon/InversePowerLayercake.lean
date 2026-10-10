module
public import FourPapersCommon.TruncatedPowerIntegrals

@[expose] public section

/-! Exact power-tail integrals used by the four isolation level sets. -/
noncomputable section
open MeasureTheory Set intervalIntegral
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem integrableOn_truncated_inverse_power_local (h b p u : ℝ)
    (hh : 0 ≤ h) (hb : 0 ≤ b) :
    IntegrableOn (fun A : ℝ => min h (b * A ^ (-p))) (Ioo 0 u) := by
  refine Integrable.of_bound
    ((measurable_const.min (measurable_const.mul (measurable_id.pow_const _))).aestronglyMeasurable)
    h ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with A hA
  rw [Real.norm_of_nonneg (le_min hh (mul_nonneg hb (Real.rpow_nonneg hA.1.le _)))]
  exact min_le_left _ _

theorem inverse_power_threshold_integral (h b p a : ℝ)
    (hh : 0 < h) (hb : 0 ≤ b) (hp : 1 < p) (ha : 0 < a)
    (hthreshold : b * a ^ (-p) = h) :
    IntegrableOn (fun A : ℝ => min h (b * A ^ (-p))) (Ioi 0) ∧
      (∫ A : ℝ in Ioi 0, min h (b * A ^ (-p))) = p / (p - 1) * h * a := by
  let f : ℝ → ℝ := fun A => min h (b * A ^ (-p))
  have he0 : EqOn f (fun _ => h) (Ioo 0 a) := by
    intro A hA
    apply min_eq_left
    rw [← hthreshold]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hA.1 hA.2.le (by linarith)) hb
  have het : EqOn f (fun A => b * A ^ (-p)) (Ioi a) := by
    intro A hA
    apply min_eq_right
    rw [← hthreshold]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hA.le (by linarith)) hb
  have hi0 : IntervalIntegrable f volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
      (integrableOn_truncated_inverse_power_local h b p a hh.le hb)
  have hip : IntegrableOn (fun A : ℝ => b * A ^ (-p)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) ha).const_mul b
  have hit : IntegrableOn f (Ioi a) :=
    hip.congr_fun (fun A hA => (het hA).symm) measurableSet_Ioi
  have hi : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp hi0).union hit
  refine ⟨hi, ?_⟩
  have heI0 : (∫ A : ℝ in 0..a, f A) = a * h := by
    rw [integral_congr_Ioo_of_le ha.le he0]
    simp
  have hepow : a ^ (-p + 1) = a * a ^ (-p) := by
    rw [show -p + 1 = 1 + -p by ring, Real.rpow_add ha, Real.rpow_one]
  have heIt : (∫ A : ℝ in Ioi a, f A) = a * h / (p - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi het, MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith : -p < -1) ha, hepow]
    rw [← hthreshold]
    field_simp [show -p + 1 ≠ 0 by linarith, show p - 1 ≠ 0 by linarith]
    ring
  have heI := integral_interval_add_Ioi hi hit
  rw [heI0, heIt] at heI
  rw [← heI]
  field_simp [show p - 1 ≠ 0 by linarith]
  ring

theorem integral_truncated_inverse_power (h b p : ℝ)
    (hh : 0 < h) (hb : 0 ≤ b) (hp : 1 < p) :
    IntegrableOn (fun A : ℝ => min h (b * A ^ (-p))) (Ioi 0) ∧
      (∫ A : ℝ in Ioi 0, min h (b * A ^ (-p))) =
        p / (p - 1) * b ^ (1 / p) * h ^ (1 - 1 / p) := by
  have hpp : 0 < p := zero_lt_one.trans hp
  by_cases hb0 : b = 0
  · subst b
    have hpinv : p⁻¹ ≠ 0 := inv_ne_zero hpp.ne'
    simp [min_eq_right hh.le, Real.zero_rpow hpinv]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  let a : ℝ := (b / h) ^ (1 / p)
  have ha : 0 < a := Real.rpow_pos_of_pos (div_pos hbp hh) _
  have hea : a ^ p = b / h := by
    dsimp only [a]
    rw [← Real.rpow_mul (div_nonneg hb hh.le),
      show (1 / p) * p = 1 by field_simp, Real.rpow_one]
  have hthreshold : b * a ^ (-p) = h := by
    rw [Real.rpow_neg ha.le, hea]
    field_simp
  obtain ⟨hi, he⟩ := inverse_power_threshold_integral h b p a hh hb hp ha hthreshold
  refine ⟨hi, he.trans ?_⟩
  have heh : h ^ (1 - 1 / p) = h / h ^ (1 / p) := by
    rw [Real.rpow_sub hh, Real.rpow_one]
  dsimp only [a]
  rw [Real.div_rpow hb hh.le, heh]
  ring

theorem integral_truncated_inverse_square (b : ℝ) (hb : 0 ≤ b) :
    IntegrableOn (fun A : ℝ => min 1 (b / A ^ 2)) (Ioi 0) ∧
      (∫ A : ℝ in Ioi 0, min 1 (b / A ^ 2)) = 2 * Real.sqrt b := by
  obtain ⟨hi, he⟩ := integral_truncated_inverse_power 1 b 2 zero_lt_one hb (by norm_num)
  have hfun : EqOn (fun A : ℝ => min 1 (b * A ^ (-(2 : ℝ))))
      (fun A => min 1 (b / A ^ 2)) (Ioi 0) := by
    intro A hA
    change min 1 (b * A ^ (-(2 : ℝ))) = min 1 (b / A ^ 2)
    rw [Real.rpow_neg hA.le]
    norm_num only [Real.rpow_two, div_eq_mul_inv]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun] at he
  refine ⟨hi.congr_fun hfun measurableSet_Ioi, ?_⟩
  convert he using 1
  norm_num [Real.sqrt_eq_rpow]

theorem integral_truncated_inverse_fourth (b : ℝ) (hb : 0 ≤ b) :
    IntegrableOn (fun A : ℝ => min 1 (b / A ^ 4)) (Ioi 0) ∧
      (∫ A : ℝ in Ioi 0, min 1 (b / A ^ 4)) = (4 / 3) * b ^ (1 / 4 : ℝ) := by
  obtain ⟨hi, he⟩ := integral_truncated_inverse_power 1 b 4 zero_lt_one hb (by norm_num)
  have hfun : EqOn (fun A : ℝ => min 1 (b * A ^ (-(4 : ℝ))))
      (fun A => min 1 (b / A ^ 4)) (Ioi 0) := by
    intro A hA
    change min 1 (b * A ^ (-(4 : ℝ))) = min 1 (b / A ^ 4)
    rw [Real.rpow_neg hA.le, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    simp only [div_eq_mul_inv]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun] at he
  refine ⟨hi.congr_fun hfun measurableSet_Ioi, ?_⟩
  convert he using 1
  norm_num

end FourPapersCommon
