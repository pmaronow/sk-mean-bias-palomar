module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! Genuine logarithmic constants for the literal cubic-moment estimate. -/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem two_thirds_le_log_two : (2/3:ℝ)≤Real.log 2 := by
  have hi : IntervalIntegrable (fun x : ℝ=>1/x) volume 1 2:=
    (continuousOn_const.div continuousOn_id (fun x hx=>ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))).intervalIntegrable_of_Icc (by norm_num)
  have hg : IntervalIntegrable (fun x : ℝ=>(4/3:ℝ)-(4/9:ℝ)*x) volume 1 2:=
    (continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable 1 2
  have hm:=intervalIntegral.integral_mono_on (by norm_num : (1:ℝ)≤2) hg hi (fun x hx=>by
    apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hx.1)).mpr
    nlinarith [sq_nonneg (2*x-3)])
  have hid : IntervalIntegrable (fun x : ℝ=>x) volume 1 2:=continuous_id.intervalIntegrable 1 2
  have hval : (∫x : ℝ in 1..2,(4/3:ℝ)-(4/9:ℝ)*x)=(2/3:ℝ):=by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hid.const_mul _),
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
    norm_num
  rw [hval,integral_one_div_of_pos zero_lt_one (by norm_num)] at hm
  simpa only [div_one] using hm

theorem two_le_log_two_div {z : ℝ} (hz : 0<z) (hzq : z≤1/4) :
    2≤Real.log (2/z) := by
  have hq : (8:ℝ)≤2/z :=(le_div_iff₀ hz).mpr (by linarith)
  have hm:=Real.log_le_log (by norm_num : (0:ℝ)<8) hq
  have he : Real.log (8:ℝ)=3*Real.log 2:=by
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num
  rw [he] at hm
  linarith [two_thirds_le_log_two]

theorem bin_tail_constant_bound (M s : ℝ) (hM : 1≤M) (hs : s∈Ioc (0:ℝ) (1/2)) :
    2/M+32*(1/(M*s))*Real.log M≤34*(1/(M*s))*Real.log (2*M) :=by
  have hMp : 0<M:=lt_of_lt_of_le zero_lt_one hM
  have he:=Real.log_mul (by norm_num : (2:ℝ)≠0) hMp.ne'
  have hlogM : 0≤Real.log M:=Real.log_nonneg hM
  have hlog2:=two_thirds_le_log_two
  have hMs : 0<M*s:=mul_pos hMp hs.1
  have hL : 2/M+32*(1/(M*s))*Real.log M=(2*s+32*Real.log M)/(M*s):=by field_simp [hMp.ne',hs.1.ne'] <;> ring
  have hR : 34*(1/(M*s))*Real.log (2*M)=34*Real.log (2*M)/(M*s):=by ring
  rw [hL,hR]
  apply (div_le_div_iff_of_pos_right hMs).mpr
  rw [he]
  nlinarith [hs.2]

end FourPapersCommon
