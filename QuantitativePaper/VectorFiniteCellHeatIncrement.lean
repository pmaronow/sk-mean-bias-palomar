module
public import QuantitativePaper.VectorFiniteCellHeat

@[expose] public section

/-! Closed subinterval heat evolution for every genuine finite profile cell.
The heat state may start before the cell, which permits a single Gaussian
state in the global finite-grid telescope. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000

theorem vectorFiniteCell_heat_increment {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (q a b : ℝ) (hqa : q≤a) (hab : a≤b) (hb : b ≤ s.q (i+1)) (x : Field n) :
    vectorFiniteCellHeatValue s β t p i q b x-vectorFiniteCellHeatValue s β t p i q a x=
      -((1-t)*β^2)/2*(s.m i)*∫ r in a..b,vectorFiniteCellGradientHeat s β t p i q r x := by
  let A : ℝ≥0 := (a-q).toNNReal
  let B : ℝ≥0 := (b-q).toNNReal
  have hA : q+(A : ℝ)=a := by dsimp only [A];rw [Real.coe_toNNReal _ (sub_nonneg.mpr hqa)];ring
  have hB : q+(B : ℝ)=b := by dsimp only [B];rw [Real.coe_toNNReal _ (sub_nonneg.mpr (hqa.trans hab))];ring
  have ha := vectorFiniteCell_heat_identity s β t hβ ht p i hi q A
    (by rw [hA];exact hab.trans hb) x
  have hbb := vectorFiniteCell_heat_identity s β t hβ ht p i hi q B (by rw [hB];exact hb) x
  rw [hA] at ha
  rw [hB] at hbb
  have hint := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_vectorFiniteCellGradientHeat s β t p i q q a x)
    (intervalIntegrable_vectorFiniteCellGradientHeat s β t p i q a b x)
  rw [←hint,mul_add] at hbb
  linarith

end QuantitativePaper
