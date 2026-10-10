module
public import FourPapersCommon.TruncatedPowerIntegrals

@[expose] public section

/-! Genuine reciprocal-tail integration after reserving a strip of width
1/M. No tail integral is supplied as an assumption. -/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem truncated_reciprocal_cutoff_bound (h b M : ℝ) (hh : 0≤h) (hh1 : h≤1)
    (hb : 0≤b) (hM : 1≤M) :
    (∫x in Ioo (0:ℝ) h,min 1 (b/x))≤1/M+b*Real.log M := by
  have hMp : 0<M:=lt_of_lt_of_le zero_lt_one hM
  let a : ℝ:=1/M
  have ha : 0<a:=by positivity
  have hi : IntervalIntegrable (fun x : ℝ=>min 1 (b/x)) volume 0 h :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hh).mpr
      (integrableOn_truncated_reciprocal 1 b h zero_le_one hb)
  rw [← integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hh]
  by_cases hha : h≤a
  · have hc:=intervalIntegral.integral_mono hh hi (intervalIntegrable_const) (fun x=>min_le_left 1 (b/x))
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hc
    have hl : 0≤b*Real.log M:=mul_nonneg hb (Real.log_nonneg hM)
    dsimp only [a] at hha
    linarith
  · have hah : a<h:=lt_of_not_ge hha
    have hi0 : IntervalIntegrable (fun x : ℝ=>min 1 (b/x)) volume 0 a :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
        (integrableOn_truncated_reciprocal 1 b a zero_le_one hb)
    have hi1 : IntervalIntegrable (fun x : ℝ=>min 1 (b/x)) volume a h :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hah.le).mpr
        ((integrableOn_truncated_reciprocal 1 b h zero_le_one hb).mono_set
          (fun _ hx=>⟨ha.trans hx.1,hx.2⟩))
    rw [←integral_add_adjacent_intervals hi0 hi1]
    have h0:=intervalIntegral.integral_mono ha.le hi0 (intervalIntegrable_const)
      (fun x=>min_le_left 1 (b/x))
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at h0
    have hiRec : IntervalIntegrable (fun x : ℝ=>b*(1/x)) volume a h :=
      ((continuousOn_const.div continuousOn_id (fun x hx=>ne_of_gt (ha.trans_le hx.1))).intervalIntegrable_of_Icc hah.le).const_mul b
    have h1:=intervalIntegral.integral_mono hah.le hi1 hiRec (fun x=>by
      simpa only [div_eq_mul_inv,one_mul] using min_le_right 1 (b/x))
    rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos ha (ha.trans hah)] at h1
    have hquot : h/a≤M:=by dsimp only [a];simp only [div_div_eq_mul_div,div_one];nlinarith
    have hlog:=Real.log_le_log (div_pos (ha.trans hah) ha) hquot
    have hbLog:=mul_le_mul_of_nonneg_left hlog hb
    dsimp only [a] at h0
    linarith

theorem integral_reflected_truncated_reciprocal (l r b : ℝ) (hlr : l≤r) :
    (∫v in Ioo l r,min 1 (b/(r-v)))=(∫x in Ioo (0:ℝ) (r-l),min 1 (b/x)) := by
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hlr,
    ←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (sub_nonneg.mpr hlr)]
  simpa only [sub_self] using intervalIntegral.integral_comp_sub_left (a:=l) (b:=r) (fun x : ℝ=>min 1 (b/x)) r

theorem integral_translated_truncated_reciprocal (l r b : ℝ) (hlr : l≤r) :
    (∫v in Ioo l r,min 1 (b/(v-l)))=(∫x in Ioo (0:ℝ) (r-l),min 1 (b/x)) := by
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hlr,
    ←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (sub_nonneg.mpr hlr)]
  simpa only [sub_self] using intervalIntegral.integral_comp_sub_right (a:=l) (b:=r) (fun x : ℝ=>min 1 (b/x)) l

end FourPapersCommon
