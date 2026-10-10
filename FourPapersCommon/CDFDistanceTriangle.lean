module
public import Paper.ParisiCDFGrid
public import Mathlib.Tactic

@[expose] public section

/-! Metric inequalities for the literal L1 distance of actual Parisi CDFs. -/
noncomputable section
open Set MeasureTheory Paper
namespace FourPapersCommon

theorem parisiCDFDistance_triangle (μ ν tau : Paper.ParisiMeasure) :
    parisiCDFDistance μ tau ≤ parisiCDFDistance μ ν + parisiCDFDistance ν tau := by
  have hi₁ := parisiCDF_abs_diff_intervalIntegrable μ ν 0 1
  have hi₂ := parisiCDF_abs_diff_intervalIntegrable ν tau 0 1
  have hi₃ := parisiCDF_abs_diff_intervalIntegrable μ tau 0 1
  have hh := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    hi₃ (hi₁.add hi₂) (fun x _ => abs_sub_le (parisiCDF μ x) (parisiCDF ν x) (parisiCDF tau x))
  rw [intervalIntegral.integral_add hi₁ hi₂] at hh
  exact hh

theorem parisiCDFDistance_symm (μ ν : Paper.ParisiMeasure) :
    parisiCDFDistance μ ν = parisiCDFDistance ν μ := by
  unfold parisiCDFDistance
  apply intervalIntegral.integral_congr
  intro x _
  exact abs_sub_comm _ _

theorem parisiCDFDistance_le_one (μ ν : Paper.ParisiMeasure) :
    parisiCDFDistance μ ν ≤ 1 := by
  have hh := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (parisiCDF_abs_diff_intervalIntegrable μ ν 0 1) (intervalIntegrable_const (c := (1 : ℝ)))
    (fun x _ => by
      rw [abs_le]
      constructor <;> linarith [parisiCDF_nonneg μ x, parisiCDF_nonneg ν x,
        parisiCDF_le_one μ x, parisiCDF_le_one ν x])
  simpa only [parisiCDFDistance, intervalIntegral.integral_const,
    sub_zero, one_smul] using hh

end FourPapersCommon
