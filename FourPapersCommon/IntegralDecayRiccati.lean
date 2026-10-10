module
public import FourPapersCommon.IntegralRiccati

@[expose] public section

/-! An exact integral evolution supplies the absolute continuity, genuine
almost-everywhere derivative, and monotonicity used by reciprocal integration. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem integral_decay_curve_regular {φ f : ℝ → ℝ} {r q : ℝ}
    (hrq : r ≤ q) (hf : IntervalIntegrable f volume r q)
    (hfn : ∀ x ∈ Icc r q, 0 ≤ f x)
    (heq : ∀ x ∈ Icc r q, φ x = φ r - ∫ u in r..x, f u) :
    AbsolutelyContinuousOnInterval φ r q ∧ AntitoneOn φ (Icc r q) ∧
      (∀ᵐ x : ℝ, x ∈ Icc r q → HasDerivAt φ (-f x) x) := by
  have hrU : r ∈ uIcc r q := left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => φ r) r q :=
    (LipschitzWith.const (φ r)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hF := hc.sub (hf.absolutelyContinuousOnInterval_intervalIntegral hrU)
  have hφ : AbsolutelyContinuousOnInterval φ r q := hF.congr (by
    intro x hx
    rw [uIcc_of_le hrq] at hx
    exact (heq x hx).symm)
  have hmono : AntitoneOn φ (Icc r q) := by
    intro x hx y hy hxy
    have hxr : IntervalIntegrable f volume r x := hf.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le hrq]
      exact Icc_subset_Icc le_rfl hx.2)
    have hixy : IntervalIntegrable f volume x y := hf.mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le hrq]
      exact Icc_subset_Icc hx.1 hy.2)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hxr hixy
    have hpos : 0 ≤ ∫ u in x..y, f u := intervalIntegral.integral_nonneg hxy
      (fun u hu => hfn u ⟨hx.1.trans hu.1, hu.2.trans hy.2⟩)
    rw [heq y hy, heq x hx]
    linarith
  have hae : ∀ᵐ x : ℝ, x ∈ Icc r q → HasDerivAt φ (-f x) x := by
    have h₁ : ∀ᵐ x : ℝ, x ≠ r := by simp [ae_iff, measure_singleton]
    have h₂ : ∀ᵐ x : ℝ, x ≠ q := by simp [ae_iff, measure_singleton]
    filter_upwards [hf.ae_hasDerivAt_integral, h₁, h₂] with x hd hxr hxq hx
    have hxU : x ∈ uIcc r q := by rwa [uIcc_of_le hrq]
    have hxO : x ∈ Ioo r q := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxr), lt_of_le_of_ne hx.2 hxq⟩
    apply ((hd hxU r hrU).const_sub (φ r)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hxO.1 hxO.2] with y hy
    exact heq y ⟨hy.1.le, hy.2.le⟩
  exact ⟨hφ, hmono, hae⟩

theorem integral_decay_riccati_bound {φ f g : ℝ → ℝ} {r q B : ℝ}
    (hrq : r ≤ q) (hB : 0 < B)
    (hf : IntervalIntegrable f volume r q)
    (hfn : ∀ x ∈ Icc r q, 0 ≤ f x)
    (heq : ∀ x ∈ Icc r q, φ x = φ r - ∫ u in r..x, f u)
    (hnonneg : ∀ x ∈ Icc r q, 0 ≤ φ x)
    (hreact : ∀ᵐ x : ℝ, x ∈ Icc r q → g x * (φ x)^2 ≤ B * f x)
    (hg : IntervalIntegrable g volume r q)
    (hden : 0 < ∫ x in r..q, g x) :
    φ q ≤ B / (∫ x in r..q, g x) := by
  obtain ⟨hφ, hmono, hder⟩ := integral_decay_curve_regular hrq hf hfn heq
  exact integral_riccati_bound hrq hB hφ hmono hnonneg hder hreact hg hden

end FourPapersCommon
