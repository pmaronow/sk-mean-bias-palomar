module
public import QuantitativePaper.VectorMeasureState
public import QuantitativePaper.VectorAdditiveIto

@[expose] public section

/-! The actual arbitrary-profile state supplies every bounded-drift Itô
characteristic; no separately tilted-law identification is presupposed. -/
noncomputable section
namespace QuantitativePaper
variable {n : ℕ}

theorem vectorItoCharacteristics_vectorMeasureState (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    VectorItoCharacteristics (vectorMeasureState (n := n) μ β t ht)
      (vectorAdditiveDrift (vectorMeasureDriftData μ β t ht)
        (Real.sqrt ((1-t)*β^2)) 0 1) (Real.sqrt ((1-t)*β^2)) :=
  vectorItoCharacteristics_vectorAdditiveState _ _ _ _

end QuantitativePaper
