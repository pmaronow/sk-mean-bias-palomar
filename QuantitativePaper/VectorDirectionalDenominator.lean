module
public import QuantitativePaper.VectorDirectionalDecay

@[expose] public section

/-! The directional decay denominator may be bounded using the CDF at any
earlier level, not just the root atom. -/
noncomputable section
open MeasureTheory Set
namespace QuantitativePaper

theorem vectorDirectionDenominator_lower_at (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (p r q : Paper.Overlap) (hpr : p≤r) (hrq : r≤q) :
    ((1-t)*β^2)*(Paper.parisiCDF μ p)^2*((q:ℝ)-r)≤
      ((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2 := by
  have hp : Monotone (fun u=>(Paper.parisiCDF μ u)^2) := fun x y hxy=>
    pow_le_pow_left₀ (Paper.parisiCDF_nonneg μ x) ((Paper.parisiCDF_monotone μ) hxy) 2
  have hI : ((q:ℝ)-r)*(Paper.parisiCDF μ p)^2≤∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2 := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hrq
      (f:=fun _ : ℝ=>(Paper.parisiCDF μ p)^2) intervalIntegrable_const hp.intervalIntegrable
      (fun u hu=>pow_le_pow_left₀ (Paper.parisiCDF_nonneg μ p)
        ((Paper.parisiCDF_monotone μ) ((show (p:ℝ)≤r from hpr).trans hu.1)) 2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  calc
    _ = ((1-t)*β^2)*(((q:ℝ)-r)*(Paper.parisiCDF μ p)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))

end QuantitativePaper
