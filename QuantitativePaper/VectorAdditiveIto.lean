module
public import QuantitativePaper.VectorAdditiveL2
public import QuantitativePaper.VectorItoCharacteristics

@[expose] public section

/-! Every characteristic required by the genuine vector Itô expectation
proof is discharged by the actual integral-Picard/Wiener construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace QuantitativePaper
variable {n : ℕ}

theorem vectorItoCharacteristics_vectorAdditiveState
    (d : VectorAdditiveDriftData n) (σ : ℝ) (x0 : Field n) (T : ℝ≥0) :
    VectorItoCharacteristics (vectorAdditiveState d σ x0 T)
      (vectorAdditiveDrift d σ x0 T) σ where
  continuous_state := continuous_vectorAdditiveState d σ x0 T
  measurable_state := measurable_uncurry_vectorAdditiveState d σ x0 T
  adapted_state := stronglyAdapted_vectorAdditiveState d σ x0 T
  measurable_drift := measurable_uncurry_vectorAdditiveDrift d σ x0 T
  bounded_drift := ⟨d.bound,norm_vectorAdditiveDrift_le d σ x0 T⟩
  decomposition := by
    intro q sample
    rw [vectorAdditiveState_zero,vectorAdditiveState_decomposition]
    abel

end QuantitativePaper
