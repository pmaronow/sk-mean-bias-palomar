module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsTerminal

@[expose] public section

/-! The receiver's chosen defect is the literal overlap of the retained
old leaf and new continuation leaf, or the two current continuation leaves,
at their genuine common ancestor. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n J : ℕ}

theorem nativeStreamingGeneratedVertex_originalFresh_test_record
    {E : Type} (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T)
    (z : Records E (Configuration (n+1)) (finiteCascadeContinuationGraft observationLinearTree v)) :
    nativeStreamingOriginalFreshSpinTest T F i
      (q (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v))
      (nativeStreamingGeneratedVertexTerminalProjection .single v (finiteCascadeRecordTerminalSpins _ z)) =
    F (finiteCascadeRecordTerminalSpins T (finiteCascadeContinuationRecords observationLinearTree v z).1) *
      cavitySpinOverlapDefect n
        (q (observationCommonLevel (finiteCascadeContinuationGraft observationLinearTree v)
          (finiteCascadeContinuationOldLeaf observationLinearTree v i)
          (finiteCascadeContinuationNewLeaf observationLinearTree v (observationLinearLeaf v.depth))))
        (observationLeafSpin _ (finiteCascadeContinuationOldLeaf observationLinearTree v i) z)
        (observationLeafSpin _
          (finiteCascadeContinuationNewLeaf observationLinearTree v (observationLinearLeaf v.depth)) z) := by
  rw [nativeStreamingGeneratedVertexTerminalProjection_record,
    finiteCascadeContinuationExtract_eq_records]
  simp only [nativeStreamingOriginalFreshSpinTest,finiteCascadeContinuationOldNewLeaf_commonLevel,
    finiteCascadeContinuationOldLeaf_spin,finiteCascadeContinuationNewLeaf_spin,
    observationTerminalSpin_record,nativeStreamingGeneratedLinearLeaf_spin,
    NativeStreamingGeneratedVertexKind.recordMark,NativeStreamingGeneratedVertexKind.continuation]

theorem nativeStreamingGeneratedVertex_current_test_record
    {E : Type} (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (z : Records E (Configuration (n+1)) (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)) :
    nativeStreamingDefectSpinTest T F (q v.depth)
      (nativeStreamingGeneratedVertexTerminalProjection .current v (finiteCascadeRecordTerminalSpins _ z)) =
    F (finiteCascadeRecordTerminalSpins T (finiteCascadeContinuationRecords nativeStreamingCurrentPairTree v z).1) *
      cavitySpinOverlapDefect n
        (q (observationCommonLevel (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)
          (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v (Sum.inl (observationLinearLeaf v.depth)))
          (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v (Sum.inr (observationLinearLeaf v.depth)))))
        (observationLeafSpin _
          (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v (Sum.inl (observationLinearLeaf v.depth))) z)
        (observationLeafSpin _
          (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v (Sum.inr (observationLinearLeaf v.depth))) z) := by
  rw [nativeStreamingGeneratedVertexTerminalProjection_record,
    finiteCascadeContinuationExtract_eq_records]
  simp only [nativeStreamingDefectSpinTest,finiteCascadeContinuationNewLeaf_commonLevel,
    finiteCascadeContinuationNewLeaf_spin,nativeStreamingCurrentPairTree,observationCommonLevel,
    observationLeafSpin,Sum.elim_inl,Sum.elim_inr,nativeStreamingGeneratedLinearLeaf_spin,
    NativeStreamingGeneratedVertexKind.recordMark,NativeStreamingGeneratedVertexKind.continuation,
    nativeStreamingCurrentPairExtract,Prod.map_apply]
  rfl

end QuantitativeFollowup
