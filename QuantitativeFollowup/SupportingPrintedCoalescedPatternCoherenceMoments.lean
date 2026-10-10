module
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceStates

@[expose] public section

/-! Genuine source moments identify both ends of every zero-time edge,
including edges nested under arbitrary advances and forks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem nativeStreamingPatternMoment_originalFresh_edge_same_time
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (i : ObservationLeaf T)
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth) :
    nativeStreamingPatternMoment D μ a q T F
        (.originalFresh i (.vertex (nativeStreamingEdgeParentVertex e))) =
      nativeStreamingPatternMoment D μ a q T F
        (.originalFresh i (.vertex (nativeStreamingEdgeChildVertex e))) := by
  have hc : q (nativeStreamingEdgeParentVertex e).depth =
      q (nativeStreamingEdgeChildVertex e).depth := by
    rw [nativeStreamingEdgeParentVertex_depth,nativeStreamingEdgeChildVertex_depth,he]
  have hp := nativeStreamingSingleVertexProbability_eq_of_clock_state D μ a q hq hzero T
    (nativeStreamingEdgeParentVertex e) (nativeStreamingEdgeChildVertex e) hc
    (nativeStreamingRecordedLaw_edge_same_time_coherent D μ a q T e he)
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginSingleProbability,
    nativeStreamingOriginCommonClock]
  rw [hp,nativeStreamingCommonClock_edge_same_time q e he]

theorem nativeStreamingPatternMoment_current_edge_same_time
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth) :
    Paper.parisiCDF μ (q (nativeStreamingEdgeParentVertex e).depth) *
        nativeStreamingPatternMoment D μ a q T F
          (.current (.vertex (nativeStreamingEdgeParentVertex e))) =
      Paper.parisiCDF μ (q (nativeStreamingEdgeChildVertex e).depth) *
        nativeStreamingPatternMoment D μ a q T F
          (.current (.vertex (nativeStreamingEdgeChildVertex e))) := by
  have hc : q (nativeStreamingEdgeParentVertex e).depth =
      q (nativeStreamingEdgeChildVertex e).depth := by
    rw [nativeStreamingEdgeParentVertex_depth,nativeStreamingEdgeChildVertex_depth,he]
  have hp := nativeStreamingCurrentPairProbability_eq_of_clock_state D μ a q hq hzero T
    (nativeStreamingEdgeParentVertex e) (nativeStreamingEdgeChildVertex e) hc
    (nativeStreamingRecordedLaw_edge_same_time_coherent D μ a q T e he)
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginCurrentProbability,
    nativeStreamingOriginLevel]
  rw [hc,hp]

theorem nativeStreamingPatternMoment_cross_vertex_edge_same_time_left
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth)
    (w : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeParentVertex e)) (.vertex w)) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeChildVertex e)) (.vertex w)) := by
  have hc : q (nativeStreamingEdgeParentVertex e).depth =
      q (nativeStreamingEdgeChildVertex e).depth := by
    rw [nativeStreamingEdgeParentVertex_depth,nativeStreamingEdgeChildVertex_depth,he]
  have hp := nativeStreamingCrossVertexProbability_left_eq_of_clock_state D μ a q hq hzero T
    (nativeStreamingEdgeParentVertex e) (nativeStreamingEdgeChildVertex e) w hc
    (nativeStreamingRecordedLaw_edge_same_time_coherent D μ a q T e he)
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,
    nativeStreamingOriginCommonClock]
  rw [hp,nativeStreamingCoalesced_commonPath_symm T (nativeStreamingEdgeParentVertex e) w,
    nativeStreamingCoalesced_commonPath_symm T (nativeStreamingEdgeChildVertex e) w,
    nativeStreamingCommonClock_edge_same_time q e he]

theorem nativeStreamingPatternMoment_cross_vertex_edge_same_time_right
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex v) (.vertex (nativeStreamingEdgeParentVertex e))) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex v) (.vertex (nativeStreamingEdgeChildVertex e))) := by
  have hc : q (nativeStreamingEdgeParentVertex e).depth =
      q (nativeStreamingEdgeChildVertex e).depth := by
    rw [nativeStreamingEdgeParentVertex_depth,nativeStreamingEdgeChildVertex_depth,he]
  have hp := nativeStreamingCrossVertexProbability_right_eq_of_clock_state D μ a q hq hzero T
    (nativeStreamingEdgeParentVertex e) (nativeStreamingEdgeChildVertex e) v hc
    (nativeStreamingRecordedLaw_edge_same_time_coherent D μ a q T e he)
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,
    nativeStreamingOriginCommonClock]
  rw [hp,nativeStreamingCommonClock_edge_same_time q e he]

end QuantitativeFollowup
