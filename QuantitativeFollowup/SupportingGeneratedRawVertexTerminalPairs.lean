module
public import QuantitativeFollowup.SupportingGeneratedSingleOriginNewPairs

@[expose] public section

/-! Physical pair transport for an arbitrary observed genealogy. Every
unary clock is retained as supplied. The actual continuation graft keeps
all old pair defects and realizes the original/fresh and current callbacks
as literal terminal leaf-pair defects. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n J : ℕ}

/-- Old pair tags retain their physical clock, including diagonal pairs. -/
theorem cavityGeneratedRawVertexOldPair_defect
    (T : FiniteTerminalGenealogy J) (q : ℕ → Paper.Overlap)
    (k : NativeStreamingGeneratedVertexKind) (v : FiniteCascadeRecordVertex T)
    (i j : ObservationLeaf T)
    (σ : TerminalSpins (Configuration (n+1)) (finiteCascadeContinuationGraft k.continuation v)) :
    cavitySpinOverlapDefect n (q (observationCommonLevel T i j))
      (observationTerminalSpin T i (nativeStreamingGeneratedVertexTerminalProjection k v σ).1)
      (observationTerminalSpin T j (nativeStreamingGeneratedVertexTerminalProjection k v σ).1) =
    cavitySpinOverlapDefect n
      (q (observationCommonLevel (finiteCascadeContinuationGraft k.continuation v)
        (finiteCascadeContinuationOldLeaf k.continuation v i)
        (finiteCascadeContinuationOldLeaf k.continuation v j)))
      (observationTerminalSpin _ (finiteCascadeContinuationOldLeaf k.continuation v i) σ)
      (observationTerminalSpin _ (finiteCascadeContinuationOldLeaf k.continuation v j) σ) := by
  rw [finiteCascadeContinuationOldLeaf_commonLevel,
    nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf,
    nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf]

/-- The single-mark callback is the actual old/new terminal pair. -/
theorem cavityGeneratedRawVertexOriginalFreshTest_terminal
    (T : FiniteTerminalGenealogy J) (q : ℕ → Paper.Overlap)
    (v : FiniteCascadeRecordVertex T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (i : ObservationLeaf T)
    (σ : TerminalSpins (Configuration (n+1)) (finiteCascadeContinuationGraft observationLinearTree v)) :
    nativeStreamingOriginalFreshSpinTest T F i
      (q (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v))
      (nativeStreamingGeneratedVertexTerminalProjection .single v σ) =
    F (nativeStreamingGeneratedVertexTerminalProjection .single v σ).1 *
      cavitySpinOverlapDefect n
        (q (observationCommonLevel (finiteCascadeContinuationGraft observationLinearTree v)
          (finiteCascadeContinuationOldLeaf observationLinearTree v i)
          (finiteCascadeContinuationNewLeaf observationLinearTree v (observationLinearLeaf v.depth))))
        (observationTerminalSpin _ (finiteCascadeContinuationOldLeaf observationLinearTree v i) σ)
        (observationTerminalSpin _
          (finiteCascadeContinuationNewLeaf observationLinearTree v (observationLinearLeaf v.depth)) σ) := by
  unfold nativeStreamingOriginalFreshSpinTest
  rw [finiteCascadeContinuationOldNewLeaf_commonLevel]
  rw [nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf,
    nativeStreamingGeneratedVertexTerminalProjection_single_new_leaf]
  rfl

/-- The independent current marks form the two actual fresh leaves. -/
theorem cavityGeneratedRawVertexCurrentTest_terminal
    (T : FiniteTerminalGenealogy J) (q : ℕ → Paper.Overlap)
    (v : FiniteCascadeRecordVertex T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (σ : TerminalSpins (Configuration (n+1)) (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)) :
    nativeStreamingDefectSpinTest T F (q v.depth)
      (nativeStreamingGeneratedVertexTerminalProjection .current v σ) =
    F (nativeStreamingGeneratedVertexTerminalProjection .current v σ).1 *
      cavitySpinOverlapDefect n
        (q (observationCommonLevel (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)
          (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v
            (Sum.inl (observationLinearLeaf v.depth)))
          (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v
            (Sum.inr (observationLinearLeaf v.depth)))))
        (observationTerminalSpin _
          (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v
            (Sum.inl (observationLinearLeaf v.depth))) σ)
        (observationTerminalSpin _
          (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v
            (Sum.inr (observationLinearLeaf v.depth))) σ) := by
  unfold nativeStreamingDefectSpinTest
  rw [finiteCascadeContinuationNewLeaf_commonLevel]
  change F (nativeStreamingGeneratedVertexTerminalProjection .current v σ).1 *
    cavitySpinOverlapDefect n (q v.depth)
      (nativeStreamingGeneratedVertexTerminalProjection .current v σ).2.1
      (nativeStreamingGeneratedVertexTerminalProjection .current v σ).2.2 = _
  have hf := nativeStreamingGeneratedVertexTerminalProjection_current_new_leaf v σ false
  have ht := nativeStreamingGeneratedVertexTerminalProjection_current_new_leaf v σ true
  simp only [Bool.false_eq_true, if_false, Bool.true_eq, if_true] at hf ht
  rw [hf,ht]
  rfl

end QuantitativeFollowup
