module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Genuine singular power and logarithmic interval integrals used in the
small-overlap interval estimate. The power integrals include the zero endpoint. -/
noncomputable section
open Set MeasureTheory Real
namespace FourPapersCommon

theorem smallInterval_twoThird_intervalIntegrable (b : ℝ) :
    IntervalIntegrable (fun x : ℝ => x ^ (-(2:ℝ)/3)) volume 0 b :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

theorem smallInterval_sevenNinth_intervalIntegrable (b : ℝ) :
    IntervalIntegrable (fun x : ℝ => x ^ (-(7:ℝ)/9)) volume 0 b :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

theorem smallInterval_twoThird_integral (b : ℝ) :
    (∫ x in (0:ℝ)..b, x ^ (-(2:ℝ)/3)) = 3*b^((1:ℝ)/3) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num
  ring

theorem smallInterval_sevenNinth_integral (b : ℝ) :
    (∫ x in (0:ℝ)..b, x ^ (-(7:ℝ)/9)) = (9/2:ℝ)*b^((2:ℝ)/9) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num
  ring

theorem smallInterval_reciprocal_intervalIntegrable (N b : ℝ)
    (hN : 1≤N) (hb : 1/N≤b) :
    IntervalIntegrable (fun x : ℝ => 1/x) volume (1/N) b := by
  have hp : 0<1/N := by positivity
  apply intervalIntegral.intervalIntegrable_one_div
  · intro x hx
    have hx' : x∈Icc (1/N) b := by simpa only [uIcc_of_le hb] using hx
    exact (hp.trans_le hx'.1).ne'
  · exact continuous_id.continuousOn

theorem smallInterval_reciprocal_integral (N b : ℝ)
    (hN : 1≤N) (hb : 1/N≤b) :
    (∫ x in (1/N:ℝ)..b, 1/x) = Real.log (N*b) := by
  have hp : 0<1/N := by positivity
  rw [integral_one_div_of_pos hp (hp.trans_le hb)]
  congr 1
  field_simp

theorem smallInterval_reciprocal_integral_le_log (N b : ℝ)
    (hN : 1≤N) (hb : 1/N≤b) (hb1 : b≤1) :
    (∫ x in (1/N:ℝ)..b, 1/x) ≤ Real.log N := by
  have hNpos : 0<N := zero_lt_one.trans_le hN
  have hbpos : 0<b := (by positivity : 0<1/N).trans_le hb
  rw [smallInterval_reciprocal_integral N b hN hb]
  exact Real.log_le_log (mul_pos hNpos hbpos)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb1 hNpos.le)

end FourPapersCommon
