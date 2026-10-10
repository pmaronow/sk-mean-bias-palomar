module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTermDefinitions

@[expose] public section

/-! The sizes in a streaming path are consequences of the actual output
constructors. A unary observation adds no leaves; every source operation
adds at most two leaves and two history coordinates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {C : ℕ}

def cavityGeneratedStreamingInitialLeafCount (S : Fin C → CavityGeneratedSiblingShape) : ℕ :=
  cavityGeneratedForestLeafCount (cavityGeneratedInitialSiblingForest S)

theorem cavityGeneratedActualStreamingTerm_counts
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    {r m : ℕ} {W : CavityGeneratedConstructedForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualStreamingTerm μ a S r m W M) :
    0 < m ∧ m ≤ printedGeneratedStreamingMarkBound r ∧
      cavityGeneratedForestLeafCount W ≤
        printedGeneratedStreamingLeafBound (cavityGeneratedStreamingInitialLeafCount S) r := by
  induction H with
  | initial =>
      simp only [printedGeneratedStreamingMarkBound,printedGeneratedStreamingLeafBound,
        cavityGeneratedStreamingInitialLeafCount,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
      exact ⟨by decide,le_rfl,le_rfl⟩
  | original previous c b e ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ]
      exact ⟨ih.1,by omega,by omega⟩
  | originalFresh previous c b γ ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedSingleOriginChartForest_leafCount]
      simp only [NativeStreamingGeneratedVertexKind.newLeafCount]
      exact ⟨by omega,by omega,by omega⟩
  | cross previous c γ δ χ ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedCrossOriginChartForest_leafCount]
      exact ⟨by omega,by omega,by omega⟩
  | current previous c γ ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedSingleOriginChartForest_leafCount]
      simp only [NativeStreamingGeneratedVertexKind.newLeafCount]
      exact ⟨by omega,by omega,by omega⟩
  | future previous c γ j ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedFutureOriginChartForest_leafCount]
      exact ⟨by omega,by omega,by omega⟩
  | normalizer previous c ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedNormalizerFamily_leafCount]
      exact ⟨by omega,by omega,by omega⟩

end QuantitativeFollowup
