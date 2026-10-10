module
public import FourPapersCommon.InterpolationPowerIntegral

@[expose] public section

/-! Integration of all three genuine moving-cutoff rates up to physical time one. -/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace FourPapersCommon
set_option maxHeartbeats 1600000

def interpolationQuantileRate (A s t : ℝ) : ℝ :=
  min 1 (min ((A*(1-t))^(-(1/2 : ℝ))) ((A*(1-t))^(-(2/3 : ℝ))*s^(-(1/3 : ℝ))))

theorem interpolationQuantileRate_bounds (A s : ℝ) (hA : 0 < A) (hs : 0 < s)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ interpolationQuantileRate A s t ∧ interpolationQuantileRate A s t ≤ 1 := by
  have ha : 0 ≤ A*(1-t) := mul_nonneg hA.le (sub_nonneg.mpr ht.2)
  exact ⟨le_min (by norm_num) (le_min (Real.rpow_nonneg ha _) (mul_nonneg (Real.rpow_nonneg ha _) (by positivity))),
    min_le_left _ _⟩

theorem interpolationQuantileRate_intervalIntegrable (A s : ℝ) (hA : 0 < A) (hs : 0 < s) :
    IntervalIntegrable (interpolationQuantileRate A s) volume 0 1 := by
  rw [intervalIntegrable_iff]
  have hm : Measurable (interpolationQuantileRate A s) := by
    unfold interpolationQuantileRate
    fun_prop
  apply (integrableOn_const (s := uIoc (0 : ℝ) 1) (C := (1 : ℝ)) (by
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ uIcc (0 : ℝ) 1 := uIoc_subset_uIcc ht
  have hb := interpolationQuantileRate_bounds A s hA hs t (by simpa only [uIcc_of_le zero_le_one] using ht')
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

theorem integral_interpolationQuantileRate_le (A s : ℝ) (hA : 0 < A) (hs : 0 < s) :
    (∫ t in (0 : ℝ)..1, interpolationQuantileRate A s t) ≤
      3*min 1 (min (A^(-(1/2 : ℝ))) (A^(-(2/3 : ℝ))*s^(-(1/3 : ℝ)))) := by
  have hi := interpolationQuantileRate_intervalIntegrable A s hA hs
  have hhalf := interpolation_power_integral A (-(1/2 : ℝ)) hA (by norm_num)
  have hthird := interpolation_power_integral A (-(2/3 : ℝ)) hA (by norm_num)
  have h1 : (∫ t in (0 : ℝ)..1, interpolationQuantileRate A s t) ≤ 1 := by
    have h := intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const
      (fun t ht => (interpolationQuantileRate_bounds A s hA hs t ht).2)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h
  have h2 : (∫ t in (0 : ℝ)..1, interpolationQuantileRate A s t) ≤ 2*A^(-(1/2 : ℝ)) := by
    have h := intervalIntegral.integral_mono_on zero_le_one hi hhalf.1
      (fun _ _ => (min_le_right _ _).trans (min_le_left _ _))
    rw [hhalf.2] at h
    convert h using 1 <;> norm_num <;> ring
  have h3 : (∫ t in (0 : ℝ)..1, interpolationQuantileRate A s t) ≤
      3*(A^(-(2/3 : ℝ))*s^(-(1/3 : ℝ))) := by
    have h := intervalIntegral.integral_mono_on zero_le_one hi (hthird.1.mul_const (s^(-(1/3 : ℝ))))
      (fun _ _ => (min_le_right _ _).trans (min_le_right _ _))
    rw [intervalIntegral.integral_mul_const, hthird.2] at h
    convert h using 1 <;> norm_num <;> ring
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3),
    mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
  exact le_min (h1.trans (by norm_num)) (le_min (h2.trans (by have hp := Real.rpow_pos_of_pos hA (-(1/2 : ℝ)); nlinarith)) h3)

end FourPapersCommon
