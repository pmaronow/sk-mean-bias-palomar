module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTermDefinitions
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawLeafCounts

@[expose] public section

/-! Actual unary observations add no leaves. Every genuine raw source
operation adds at most two leaves and two retained history coordinates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {C : ℕ}

def cavityGeneratedObservedRawStreamingInitialLeafCount
    (S : CavityGeneratedObservedRawInitialForest C) : ℕ :=
  (cavityGeneratedObservedRawInitialForest S).leafCount

theorem cavityGeneratedActualObservedRawStreamingTerm_counts
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M) :
    0 < m ∧ m ≤ printedGeneratedStreamingMarkBound r ∧
      W.leafCount ≤ printedGeneratedStreamingLeafBound
        (cavityGeneratedObservedRawStreamingInitialLeafCount S) r := by
  induction H with
  | initial =>
      simp only [printedGeneratedStreamingMarkBound,printedGeneratedStreamingLeafBound,
        cavityGeneratedObservedRawStreamingInitialLeafCount,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
      exact ⟨by decide,le_rfl,le_rfl⟩
  | original previous c b e ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ]
      exact ⟨ih.1,by omega,by omega⟩
  | originalFresh previous c b γ ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedObservedRawSingleOriginChartForest_leafCount]
      simp only [NativeStreamingGeneratedVertexKind.newLeafCount]
      exact ⟨by omega,by omega,by omega⟩
  | cross previous c γ δ χ ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedObservedRawCrossChartForest_leafCount]
      exact ⟨by omega,by omega,by omega⟩
  | current previous c γ ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedObservedRawSingleOriginChartForest_leafCount]
      simp only [NativeStreamingGeneratedVertexKind.newLeafCount]
      exact ⟨by omega,by omega,by omega⟩
  | future previous c γ j ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedObservedRawFutureForest_leafCount]
      exact ⟨by omega,by omega,by omega⟩
  | normalizer previous c ih =>
      rw [printedGeneratedStreamingMarkBound_succ,printedGeneratedStreamingLeafBound_succ,
        cavityGeneratedObservedRawNormalizerForest_leafCount]
      exact ⟨by omega,by omega,by omega⟩

end QuantitativeFollowup
