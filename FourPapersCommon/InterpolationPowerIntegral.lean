module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Exact integrals of the genuine interpolation endpoint singularities. -/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem interpolation_power_integral (A p : ℝ) (hA : 0 < A) (hp : -1 < p) :
    IntervalIntegrable (fun t => (A*(1-t))^p) volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, (A*(1-t))^p) = A^p/(p+1) := by
  have hi : IntervalIntegrable (fun t : ℝ => t^p) volume 0 1 := intervalIntegrable_rpow' hp
  have his : IntervalIntegrable (fun t : ℝ => (1-t)^p) volume 0 1 := by
    simpa only [sub_zero, sub_self] using (hi.comp_sub_left 1).symm
  have he : (∫ t in (0 : ℝ)..1, (1-t)^p) = 1/(p+1) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^p) 1]
    simp only [sub_self, sub_zero]
    rw [integral_rpow (Or.inl hp), Real.one_rpow, Real.zero_rpow (by linarith : p+1 ≠ 0), sub_zero]
  have hiA : IntervalIntegrable (fun t : ℝ => (A*(1-t))^p) volume 0 1 := by
    apply (his.const_mul (A^p)).congr
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
    exact (Real.mul_rpow hA.le (sub_nonneg.mpr ht'.2)).symm
  refine ⟨hiA, ?_⟩
  calc
    _ = ∫ t in (0 : ℝ)..1, A^p*(1-t)^p := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      exact Real.mul_rpow hA.le (sub_nonneg.mpr ht'.2)
    _ = A^p/(p+1) := by rw [intervalIntegral.integral_const_mul, he]; ring

end FourPapersCommon
