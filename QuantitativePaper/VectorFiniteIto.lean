module
public import QuantitativePaper.VectorFiniteStateEquation
public import QuantitativePaper.VectorAdditiveIto

@[expose] public section

/-! Genuine vector Itô characteristics for the constructed finite Parisi
state; the drift is the literal finite tail gradient and Wiener increments
retain their actual enlarged-past independence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace QuantitativePaper
open SpinGlass.Targets
variable {n k : ℕ}

theorem vectorItoCharacteristics_vectorFiniteState (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) :
    VectorItoCharacteristics (vectorFiniteState (n := n) s β t ht)
      (vectorAdditiveDrift (vectorFiniteDriftData s β t ht) (Real.sqrt ((1-t)*β^2)) 0 1)
      (Real.sqrt ((1-t)*β^2)) :=
  vectorItoCharacteristics_vectorAdditiveState _ _ _ _

end QuantitativePaper
