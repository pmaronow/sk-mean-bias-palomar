module
public import FourPapersCommon.InversePowerLayercake

@[expose] public section

/-! Exact boundary-layer integral of a linearly growing cap against an
inverse-square tail, and the integrable inverse-two-thirds singularity. -/
noncomputable section
open MeasureTheory Set intervalIntegral
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem linear_inverse_square_threshold_integral (c b a : ℝ)
    (hc : 0 < c) (_hb : 0 ≤ b) (ha : 0 < a) (hthreshold : c * a ^ 3 = b) :
    IntegrableOn (fun A : ℝ => min (c * A) (b / A ^ 2)) (Ioi 0) ∧
      (∫ A : ℝ in Ioi 0, min (c * A) (b / A ^ 2)) = (3 / 2) * c * a ^ 2 := by
  let f : ℝ → ℝ := fun A => min (c * A) (b / A ^ 2)
  have he0 : EqOn f (fun A => c * A) (Ioo 0 a) := by
    intro A hA
    apply min_eq_left
    apply (le_div_iff₀ (sq_pos_of_pos hA.1)).mpr
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA.1.le hA.2.le 3) hc.le
    nlinarith
  have het : EqOn f (fun A => b * A ^ (-(2 : ℝ))) (Ioi a) := by
    intro A hA
    change min (c * A) (b / A ^ 2) = b * A ^ (-(2 : ℝ))
    rw [Real.rpow_neg (ha.trans hA).le, Real.rpow_two, ← div_eq_mul_inv]
    apply min_eq_right
    apply (div_le_iff₀ (sq_pos_of_pos (ha.trans hA))).mpr
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hA.le 3) hc.le
    nlinarith
  have hil : IntervalIntegrable (fun A : ℝ => c * A) volume 0 a :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 a
  have hilon : IntegrableOn (fun A : ℝ => c * A) (Ioo 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mp hil
  have hi0 : IntervalIntegrable f volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
      (hilon.congr_fun (fun A hA => (he0 hA).symm) measurableSet_Ioo)
  have hip : IntegrableOn (fun A : ℝ => b * A ^ (-(2 : ℝ))) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) ha).const_mul b
  have hit : IntegrableOn f (Ioi a) :=
    hip.congr_fun (fun A hA => (het hA).symm) measurableSet_Ioi
  have hi : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp hi0).union hit
  refine ⟨hi, ?_⟩
  have heI0 : (∫ A : ℝ in 0..a, f A) = c * a ^ 2 / 2 := by
    rw [integral_congr_Ioo_of_le ha.le he0, intervalIntegral.integral_const_mul, integral_id]
    ring
  have heIt : (∫ A : ℝ in Ioi a, f A) = b / a := by
    rw [setIntegral_congr_fun measurableSet_Ioi het, MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) ha]
    norm_num [Real.rpow_neg_one]
    ring
  have heI := integral_interval_add_Ioi hi hit
  rw [heI0, heIt, ← hthreshold] at heI
  rw [← heI]
  field_simp
  ring

theorem integral_linear_inverse_square (c b : ℝ) (hc : 0 < c) (hb : 0 ≤ b) :
    IntegrableOn (fun A : ℝ => min (c * A) (b / A ^ 2)) (Ioi 0) ∧
      (∫ A : ℝ in Ioi 0, min (c * A) (b / A ^ 2)) =
        (3 / 2) * c ^ (1 / 3 : ℝ) * b ^ (2 / 3 : ℝ) := by
  by_cases hb0 : b = 0
  · subst b
    have he : (fun A : ℝ => min (c * A) (0 / A ^ 2)) =ᵐ[volume.restrict (Ioi 0)]
        (fun _ => 0) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with A hA
      simp only [zero_div, min_eq_right (mul_nonneg hc.le hA.le)]
    have hiz : Integrable (fun _ : ℝ => (0 : ℝ)) (volume.restrict (Ioi 0)) :=
      integrable_zero ℝ ℝ (volume.restrict (Ioi 0))
    refine ⟨hiz.congr he.symm, ?_⟩
    rw [integral_congr_ae he]
    norm_num
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  let a : ℝ := (b / c) ^ (1 / 3 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos (div_pos hbp hc) _
  have hea : a ^ 3 = b / c := by
    dsimp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hb hc.le)]
    norm_num
  have hthreshold : c * a ^ 3 = b := by rw [hea]; field_simp
  obtain ⟨hi, he⟩ := linear_inverse_square_threshold_integral c b a hc hb ha hthreshold
  refine ⟨hi, he.trans ?_⟩
  have hepow : a ^ 2 = (b / c) ^ (2 / 3 : ℝ) := by
    dsimp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hb hc.le)]
    norm_num
  have hec : c ^ (1 / 3 : ℝ) = c / c ^ (2 / 3 : ℝ) := by
    rw [show (1 / 3 : ℝ) = 1 - 2 / 3 by norm_num, Real.rpow_sub hc, Real.rpow_one]
  rw [hepow, Real.div_rpow hb hc.le, hec]
  ring

theorem integral_min_linear_inverse_square (L b : ℝ) (hL : 0 < L) (hb : 0 ≤ b) :
    IntegrableOn (fun A : ℝ => min (A / (2 * L)) (b / A ^ 2)) (Ioi 0) ∧
      (∫ A : ℝ in Ioi 0, min (A / (2 * L)) (b / A ^ 2)) =
        3 * b ^ (2 / 3 : ℝ) / (2 * (2 * L) ^ (1 / 3 : ℝ)) := by
  obtain ⟨hi, he⟩ := integral_linear_inverse_square (1 / (2 * L)) b (by positivity) hb
  have hf : (fun A : ℝ => min ((1 / (2 * L)) * A) (b / A ^ 2)) =
      fun A => min (A / (2 * L)) (b / A ^ 2) := by
    funext A
    congr 1
    ring
  rw [hf] at hi he
  refine ⟨hi, he.trans ?_⟩
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by positivity), Real.one_rpow]
  ring

theorem integral_inverse_two_thirds (β : ℝ) (hβ : 0 ≤ β) :
    IntegrableOn (fun A : ℝ => A ^ (-(2 / 3 : ℝ))) (Ioo 0 β) ∧
      (∫ A : ℝ in Ioo 0 β, A ^ (-(2 / 3 : ℝ))) = 3 * β ^ (1 / 3 : ℝ) := by
  have hi : IntervalIntegrable (fun A : ℝ => A ^ (-(2 / 3 : ℝ))) volume 0 β :=
    intervalIntegrable_rpow' (by norm_num : -1 < -(2 / 3 : ℝ))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hβ).mp hi, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hβ,
    integral_rpow (Or.inl (by norm_num : -1 < -(2 / 3 : ℝ)))]
  norm_num
  ring

end FourPapersCommon
