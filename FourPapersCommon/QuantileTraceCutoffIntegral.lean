module
public import FourPapersCommon.ShiftedInverseSquareIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! A genuine inverse-square trace integral with a moving quantile cutoff. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem bounded_quantile_trace_cutoff_integral (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    (hb : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) (M s u : ℝ) (hM : 0 < M)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Icc s 1)
    (htail : ∀ v ∈ Ioo (0 : ℝ) (1-s), ψ v ≤ 1/(M*(s+v)^2)) :
    (∫ v in Ioo (0 : ℝ) (1-s), ψ v) ≤ (u-s)+1/(M*u) := by
  have hu0 : 0 < u := hs.1.trans_le hu.1
  have hi (a b : ℝ) : IntervalIntegrable ψ volume a b := by
    let : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
      isFiniteMeasure_restrict.mpr (by
        rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
    rw [intervalIntegrable_iff]
    exact Integrable.of_bound (μ := volume.restrict (uIoc a b)) hψ.aestronglyMeasurable 1
      (.of_forall fun v => by rw [Real.norm_of_nonneg (hb v).1]; exact (hb v).2)
  have hlow : (∫ v in (0 : ℝ)..(u-s), ψ v) ≤ u-s := by
    have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := u-s)
      (f := ψ) (g := fun _ => (1 : ℝ))
      (sub_nonneg.mpr hu.1) (hi 0 (u-s)) intervalIntegrable_const
      (fun v _ => (hb v).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
      using h
  have hhigh : (∫ v in (u-s)..(1-s), ψ v) ≤ 1/(M*u) := by
    have hinv := shifted_inverse_square_interval_integral M s (u-s) (1-s) hM
      (sub_le_sub_right hu.2 s) (by linarith)
    have hle := intervalIntegral.integral_mono_on_of_le_Ioo
      (a := u-s) (b := 1-s) (f := ψ) (g := fun v => 1/(M*(s+v)^2))
      (sub_le_sub_right hu.2 s) (hi (u-s) (1-s)) hinv.1
      (fun v hv => htail v ⟨lt_of_le_of_lt (sub_nonneg.mpr hu.1) hv.1, hv.2⟩)
    rw [hinv.2] at hle
    have hn : 0 ≤ 1/(M*(s+(1-s))) := by
      have he : s+(1-s) = 1 := by ring
      rw [he, mul_one]
      positivity
    have he : s+(u-s)=u := by ring
    rw [he] at hle
    linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 (u-s)) (hi (u-s) (1-s))
  have he : (∫ v in (0 : ℝ)..(1-s), ψ v) = ∫ v in Ioo (0 : ℝ) (1-s), ψ v := by
    rw [intervalIntegral.integral_of_le (by linarith [hs.2] : (0 : ℝ) ≤ 1-s), integral_Ioc_eq_integral_Ioo]
  rw [he] at hsplit
  linarith

end FourPapersCommon
