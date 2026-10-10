module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

/-! An actual integral representation gives absolute continuity and the
almost-everywhere derivative. Consequently every Lipschitz interval test
has the genuine weighted FTC, including its endpoint terms. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace FourPapersCommon
set_option maxHeartbeats 300000

theorem absolutelyContinuousOnInterval_of_integrable_primitive
    (F H : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hH : IntervalIntegrable H volume a b)
    (hrep : ∀ x ∈ Icc a b, F x - F a = ∫ y in a..x, H y) :
    AbsolutelyContinuousOnInterval F a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => F a) a b :=
    (LipschitzWith.const (F a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hp := hH.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  apply (hc.fun_add hp).congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hr := hrep x hx
  linarith only [hr]

theorem ae_hasDerivAt_of_integrable_primitive
    (F H : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hH : IntervalIntegrable H volume a b)
    (hrep : ∀ x ∈ Icc a b, F x - F a = ∫ y in a..x, H y) :
    ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (H x) x := by
  filter_upwards [hH.ae_hasDerivAt_integral] with x hx hxI
  have hxu : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hxI.1.le, hxI.2.le⟩
  have hp := hx hxu a (by simp)
  have hd := (hasDerivAt_const x (F a)).add hp
  simp only [zero_add] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
  have hr := hrep y ⟨hy.1.le, hy.2.le⟩
  change F y = F a + ∫ v in a..y, H v
  linarith only [hr]

theorem lipschitz_weighted_FTC_of_integrable_primitive
    (F H φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hH : IntervalIntegrable H volume a b)
    (hrep : ∀ x ∈ Icc a b, F x - F a = ∫ y in a..x, H y)
    (K : ℝ≥0) (hφ : LipschitzOnWith K φ (Icc a b)) :
    φ b * F b - φ a * F a =
      ∫ x in a..b, deriv φ x * F x + φ x * H x := by
  have hF := absolutelyContinuousOnInterval_of_integrable_primitive F H a b hab hH hrep
  have hφu : LipschitzOnWith K φ (uIcc a b) := by simpa only [uIcc_of_le hab] using hφ
  calc
    _ = ∫ x in a..b, deriv φ x * F x + φ x * deriv F x :=
      (hφu.absolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hF).symm
    _ = _ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_hasDerivAt_of_integrable_primitive F H a b hab hH hrep,
        volume.ae_ne b] with x hx hxb hxI
      rw [uIoc_of_le hab] at hxI
      rw [(hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩).deriv]

end FourPapersCommon
