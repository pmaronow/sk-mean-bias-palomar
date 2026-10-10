module
public import HexagonPaper.VariableScalarClock
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Primitive clocks for the source's positive bounded measurable
level-dependent scalar coefficient. -/
noncomputable section
open Set MeasureTheory
namespace HexagonPaper

def scalarCoefficientPrimitive (c : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..q, c r

theorem scalarCoefficient_intervalIntegrable (c : ℝ → ℝ) (L : ℝ)
    (hc : AEStronglyMeasurable c (volume.restrict (Icc (0 : ℝ) 1)))
    (hbound : ∀ q ∈ Icc (0 : ℝ) 1, ‖c q‖ ≤ L) :
    IntervalIntegrable c volume 0 1 := by
  have hint : IntegrableOn c (Icc (0 : ℝ) 1) volume := by
    apply (integrable_const L).mono' hc
    exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all volume hbound)
  have hint' : IntegrableOn c (uIcc (0 : ℝ) 1) volume := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hint
  exact hint'.intervalIntegrable

theorem scalarCoefficient_primitive_strictMonoOn (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    StrictMonoOn (scalarCoefficientPrimitive c) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have h0x : IntervalIntegrable c volume 0 x :=
    hint.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl hx.2)
  have hxyI : IntervalIntegrable c volume x y :=
    hint.mono_set (by
      rw [uIcc_of_le hxy.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc hx.1 hy.2)
  have hpositive : 0 < ∫ r in x..y, c r :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hxyI
      (fun r hr => hpos r ⟨hx.1.trans_lt hr.1, hr.2.trans_le hy.2⟩) hxy
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0x hxyI
  change (∫ r in (0 : ℝ)..x, c r) < ∫ r in (0 : ℝ)..y, c r
  linarith

theorem scalarCoefficient_total_pos (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    0 < scalarCoefficientPrimitive c 1 := by
  simpa only [scalarCoefficientPrimitive, intervalIntegral.integral_same] using
    scalarCoefficient_primitive_strictMonoOn c hint hpos
      (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)

theorem scalarCoefficient_primitive_continuousOn (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1) :
    ContinuousOn (scalarCoefficientPrimitive c) (Icc (0 : ℝ) 1) := by
  change ContinuousOn (fun q : ℝ => ∫ r in (0 : ℝ)..q, c r) (Icc (0 : ℝ) 1)
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    intervalIntegral.continuousOn_primitive_interval' hint (a := (0 : ℝ)) (by simp)

end HexagonPaper
