module
public import QuantitativePaper.VectorFiniteMildCells

@[expose] public section

/-! The genuine global finite-profile mild equation, obtained by telescoping
the proved cell Itô identities across the actual clamped overlap mesh. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

def vectorTerminalHeat {n : ℕ} (β t q : ℝ) (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  ∫ z,vectorTerminalPotential n β t p (fieldShift ((1-t)*β^2*(1-q)) x z) ∂fieldGaussian n

theorem vectorFinite_mild_equation {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    vectorTailRecursion s β t q p (k+2) x=vectorTerminalHeat β t q p x+
      ((1-t)*β^2)/2*∫ r in (q : ℝ)..1,
        vectorMildSource (Paper.parisiSchemeMeasure s) (vectorFiniteTailGradient s β t)
          ((1-t)*β^2) q r p x := by
  let a := fun i : ℕ => max (q : ℝ) (s.q i)
  let F := fun i : ℕ => vectorFiniteTailHeatValue s β t q (a i) p x
  let g := fun r : ℝ => vectorMildSource (Paper.parisiSchemeMeasure s)
    (vectorFiniteTailGradient s β t) ((1-t)*β^2) q r p x
  have ha0 : a 0=q := by simp only [a,s.q_zero,max_eq_left q.property.1]
  have haN : a (k+2)=1 := by simp only [a,s.q_top,max_eq_right q.property.2]
  have hi (i : ℕ) : IntervalIntegrable g volume (a i) (a (i+1)) :=
    intervalIntegrable_vectorMildSource (Paper.parisiSchemeMeasure s) (vectorFiniteTailGradient s β t)
      (measurable_vectorFiniteTailGradient s β t) (norm_vectorFiniteTailGradient_le s β t)
      _ _ _ _ p x
  have hint := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := k+2)
    (fun i _ => hi i)
  rw [ha0,haN] at hint
  have htel := Finset.sum_range_sub F (k+2)
  have hcells : (∑i∈Finset.range (k+2),(F (i+1)-F i))=
      -((1-t)*β^2)/2*∑i∈Finset.range (k+2),(∫r in a i..a (i+1),g r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact vectorFiniteMild_mesh_cell s β t hβ ht q p i
      (by have := Finset.mem_range.mp hi;omega) x
  rw [hint,htel] at hcells
  have hF0 : F 0=vectorTailRecursion s β t q p (k+2) x := by
    rw [show F 0=vectorFiniteTailHeatValue s β t q (a 0) p x from rfl,ha0]
    simp [vectorFiniteTailHeatValue,fieldShift]
  have hFN : F (k+2)=vectorTerminalHeat β t q p x := by
    rw [show F (k+2)=vectorFiniteTailHeatValue s β t q (a (k+2)) p x from rfl,haN]
    unfold vectorFiniteTailHeatValue vectorTerminalHeat
    rw [vectorTailRecursion_one s β t p le_rfl]
  rw [hF0,hFN] at hcells
  change vectorTerminalHeat β t q p x-vectorTailRecursion s β t q p (k+2) x=
    -((1-t)*β^2)/2*(∫r in (q : ℝ)..1,g r) at hcells
  dsimp only [g] at hcells
  linarith

end QuantitativePaper
