module
public import HexagonPaper.VariableScalarClockPrimitiveDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

/-! Actual absolute continuity and almost-everywhere derivative of the
primitive scalar clock; no continuity of the coefficient is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HexagonPaper

theorem scalarCoefficientRealClock_of_mem (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    scalarCoefficientRealClock c hint hpos x =
      scalarCoefficientPrimitive c x / scalarCoefficientPrimitive c 1 := by
  unfold scalarCoefficientRealClock
  rw [projIcc_of_mem zero_le_one hx, scalarCoefficientClock_apply]
  rfl

theorem scalarCoefficientClock_ae_hasDerivAt (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    ∀ᵐ q : ℝ ∂volume, q ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (scalarCoefficientRealClock c hint hpos)
        (c q / scalarCoefficientPrimitive c 1) q := by
  filter_upwards [hint.ae_hasDerivAt_integral] with q hq
  intro hqi
  have hqc : q ∈ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hqi.1.le, hqi.2.le⟩
  have hd := (hq hqc 0 (by simp : (0 : ℝ) ∈ uIcc 0 1)).div_const
    (scalarCoefficientPrimitive c 1)
  have heq : (fun x : ℝ => (∫ r in (0 : ℝ)..x, c r) / scalarCoefficientPrimitive c 1)
      =ᶠ[𝓝 q] scalarCoefficientRealClock c hint hpos := by
    filter_upwards [Ioo_mem_nhds hqi.1 hqi.2] with x hx
    exact (scalarCoefficientRealClock_of_mem c hint hpos ⟨hx.1.le, hx.2.le⟩).symm
  exact hd.congr_of_eventuallyEq heq.symm

theorem scalarCoefficientPrimitive_absolutelyContinuous (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1) :
    AbsolutelyContinuousOnInterval (scalarCoefficientPrimitive c) 0 1 := by
  exact hint.absolutelyContinuousOnInterval_intervalIntegral (by simp : (0 : ℝ) ∈ uIcc 0 1)

theorem scalarCoefficientRealClock_absolutelyContinuous (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    AbsolutelyContinuousOnInterval (scalarCoefficientRealClock c hint hpos) 0 1 := by
  have h := (scalarCoefficientPrimitive_absolutelyContinuous c hint).const_mul
    (scalarCoefficientPrimitive c 1)⁻¹
  apply h.congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  rw [scalarCoefficientRealClock_of_mem c hint hpos hx]
  simp only [div_eq_mul_inv, mul_comm]

end HexagonPaper
