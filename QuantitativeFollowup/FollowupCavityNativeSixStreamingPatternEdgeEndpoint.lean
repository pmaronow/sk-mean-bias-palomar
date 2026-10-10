module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeEndpointCoherenceLaws

@[expose] public section

/-! Actual original/fresh and current source moments at the upper endpoint
of a retained edge. The complete old record is preserved by the endpoint
law; the defect clock is identified from the literal common-clock formula.
Independent current fresh spins remain two separate terminal marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem nativeStreamingOriginCommonClock_edge_upper_vertex
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T) :
    nativeStreamingOriginCommonClock q T (.vertex v) (.edge e (q e.depth)) =
      nativeStreamingOriginCommonClock q T (.vertex v)
        (.vertex (nativeStreamingEdgeChildVertex e)) := by
  simp only [nativeStreamingOriginCommonClock, nativeStreamingOldSelectedCommonClock]
  split_ifs with h
  · rw [h]
  · rfl

theorem nativeStreamingPatternMoment_originalFresh_edge_upper
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (e : NativeStreamingEdge T) :
    nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.edge e (q e.depth))) =
      nativeStreamingPatternMoment D μ a q T F
        (.originalFresh i (.vertex (nativeStreamingEdgeChildVertex e))) := by
  have hp := (nativeStreamingEdgeMarkProbabilities_endpoint D μ a q hq hzero T e false).1
  simp only [nativeStreamingEndpointVertex, nativeStreamingEdgeChildVertex_depth] at hp
  simp only [nativeStreamingPatternMoment, nativeStreamingOriginSingleProbability]
  rw [nativeStreamingOriginCommonClock_edge_upper_vertex, hp]

theorem nativeStreamingPatternMoment_current_edge_upper
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) :
    nativeStreamingPatternMoment D μ a q T F (.current (.edge e (q e.depth))) =
      nativeStreamingPatternMoment D μ a q T F
        (.current (.vertex (nativeStreamingEdgeChildVertex e))) := by
  have hp := (nativeStreamingEdgeMarkProbabilities_endpoint D μ a q hq hzero T e false).2
  simp only [nativeStreamingEndpointVertex, nativeStreamingEdgeChildVertex_depth] at hp
  simp only [nativeStreamingPatternMoment, nativeStreamingOriginCurrentProbability,
    nativeStreamingOriginLevel, nativeStreamingEdgeChildVertex_depth]
  rw [hp]

end QuantitativeFollowup
