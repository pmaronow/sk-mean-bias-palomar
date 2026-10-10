module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! The actual compactly supported tent used in the response-midpoint proof. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1800000

 def responseTent (ell q : ℝ) : ℝ := max 0 (1-4*|q-ell/2|/ell)
 def responseTentSlope (ell q : ℝ) : ℝ :=
  if q<ell/4 then 0 else if q<ell/2 then 4/ell else if q<3*ell/4 then -(4/ell) else 0

 theorem continuous_responseTent (ell : ℝ) : Continuous (responseTent ell) := by
  unfold responseTent
  fun_prop

 theorem responseTent_left_formula {ell q : ℝ} (hell : 0<ell)
    (hq : q∈Icc (ell/4) (ell/2)) : responseTent ell q=4*q/ell-1 := by
  unfold responseTent
  rw [abs_of_nonpos (by linarith [hq.2] : q-ell/2≤0)]
  have he : 1-4*(-(q-ell/2))/ell=4*q/ell-1 := by field_simp; ring
  rw [he,max_eq_right]
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hell).mpr
  linarith [hq.1]

 theorem responseTent_right_formula {ell q : ℝ} (hell : 0<ell)
    (hq : q∈Icc (ell/2) (3*ell/4)) : responseTent ell q=3-4*q/ell := by
  unfold responseTent
  rw [abs_of_nonneg (by linarith [hq.1] : 0≤q-ell/2)]
  have he : 1-4*(q-ell/2)/ell=3-4*q/ell := by field_simp; ring
  rw [he,max_eq_right]
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hell).mpr
  linarith [hq.2]

 theorem responseTent_zero_left {ell q : ℝ} (hell : 0<ell) (hq : q≤ell/4) :
    responseTent ell q=0 := by
  unfold responseTent
  rw [abs_of_nonpos (by linarith : q-ell/2≤0),max_eq_left]
  apply sub_nonpos.mpr
  apply (le_div_iff₀ hell).mpr
  linarith

 theorem responseTent_zero_right {ell q : ℝ} (hell : 0<ell) (hq : 3*ell/4≤q) :
    responseTent ell q=0 := by
  unfold responseTent
  rw [abs_of_nonneg (by linarith : 0≤q-ell/2),max_eq_left]
  apply sub_nonpos.mpr
  apply (le_div_iff₀ hell).mpr
  linarith

 theorem responseTent_pos_iff {ell q : ℝ} (hell : 0<ell) :
    0<responseTent ell q ↔ q∈Ioo (ell/4) (3*ell/4) := by
  unfold responseTent
  rw [lt_max_iff]
  simp only [lt_self_iff_false,false_or,sub_pos,div_lt_iff₀ hell]
  have he : 4*|q-ell/2|<1*ell ↔ |q-ell/2|<ell/4 := by constructor <;> intro h <;> linarith
  rw [he,abs_lt]
  simp only [mem_Ioo]
  constructor
  · intro h; constructor <;> linarith [h.1,h.2]
  · intro h; constructor <;> linarith [h.1,h.2]

 theorem support_responseTent {ell : ℝ} (hell : 0<ell) :
    Function.support (responseTent ell)=Ioo (ell/4) (3*ell/4) := by
  ext q
  rw [Function.mem_support,←responseTent_pos_iff hell]
  constructor
  · intro h; exact lt_of_le_of_ne (le_max_left 0 _) (Ne.symm h)
  · exact ne_of_gt

 theorem responseTent_integral_left {ell : ℝ} (hell : 0<ell) :
    (∫q in ell/4..ell/2,responseTent ell q)=ell/8 := by
  rw [intervalIntegral.integral_congr (fun q hq=>responseTent_left_formula hell
    (by simpa only [uIcc_of_le (by linarith : ell/4≤ell/2)] using hq)),
    intervalIntegral.integral_sub ((show Continuous (fun q : ℝ=>4*q/ell) by fun_prop).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_div,intervalIntegral.integral_const_mul,integral_id,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

 theorem responseTent_integral_right {ell : ℝ} (hell : 0<ell) :
    (∫q in ell/2..3*ell/4,responseTent ell q)=ell/8 := by
  rw [intervalIntegral.integral_congr (fun q hq=>responseTent_right_formula hell
    (by simpa only [uIcc_of_le (by linarith : ell/2≤3*ell/4)] using hq)),
    intervalIntegral.integral_sub intervalIntegrable_const ((show Continuous (fun q : ℝ=>4*q/ell) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_div,intervalIntegral.integral_const_mul,integral_id,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

 theorem responseTent_integral {ell : ℝ} (hell : 0<ell) :
    (∫q,responseTent ell q)=ell/4 := by
  have hs : ∫q,responseTent ell q=∫q in Ioo (ell/4) (3*ell/4),responseTent ell q := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun q hq=>by
      have hnot : q∉Function.support (responseTent ell) := by rwa [support_responseTent hell]
      change ¬(responseTent ell q≠0) at hnot
      exact not_not.mp hnot)).symm
  rw [hs,←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by linarith : ell/4≤3*ell/4),
    ←intervalIntegral.integral_add_adjacent_intervals
      ((continuous_responseTent ell).intervalIntegrable (ell/4) (ell/2))
      ((continuous_responseTent ell).intervalIntegrable (ell/2) (3*ell/4)),
    responseTent_integral_left hell,responseTent_integral_right hell]
  ring

end QuantitativePaper
