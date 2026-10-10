module
public import QuantitativePaper.CompletedFractionalPressureContinuity

@[expose] public section

/-! The zero-tilt expected-pressure estimate follows from the positive-tilt
estimate by the actual removable-moment limit and constrained-value
continuity. The positive-tilt bound is a separate interpolation obligation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 900000

theorem pressure_gap_of_fractional_bounds (n : ℕ) (β B : ℝ)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) (1/2),
      0 ≤ constrainedParisiValue β s - completedFractionalPressure n β s ∧
      constrainedParisiValue β s - completedFractionalPressure n β s ≤ B) :
    0 ≤ Paper.parisiPDEValue β 0 - pressure n β ∧
      Paper.parisiPDEValue β 0 - pressure n β ≤ B := by
  let sj : ℕ → ℝ := fun j => (1/2) * (1/((j : ℝ)+1))
  have hs (j : ℕ) : sj j ∈ Ioc (0 : ℝ) (1/2) := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    dsimp only [sj]
    constructor
    · positivity
    · have hd : 1/((j : ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      linarith
  have hsj : Tendsto sj atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1/2 : ℝ)
  have hsjI : Tendsto sj atTop (𝓝[Icc (0 : ℝ) 1] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsj, .of_forall fun j =>
      ⟨(hs j).1.le, (hs j).2.trans (by norm_num)⟩⟩
  have hlim := ((continuousOn_scalar_fractional_gap n β) 0 (by norm_num)).tendsto.comp hsjI
  have he : constrainedParisiValue β 0 - completedFractionalPressure n β 0 =
      Paper.parisiPDEValue β 0 - pressure n β := by
    simp only [constrainedParisiValue_zero, completedFractionalPressure, ite_true]
  rw [he] at hlim
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (.of_forall fun j => (hbound (sj j) (hs j)).1),
    le_of_tendsto_of_tendsto hlim tendsto_const_nhds
      (.of_forall fun j => (hbound (sj j) (hs j)).2)⟩

end QuantitativePaper
