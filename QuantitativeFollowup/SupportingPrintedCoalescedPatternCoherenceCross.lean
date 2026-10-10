module
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedCrossWeightsEndpoint

@[expose] public section

/-! Cross moments are coherent in either variable on genuine physical
origins. The fixed edge time is restricted to its actual closed cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingRefinement_ae_state_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hl : ∀ k, Q (observationRefinementDepth d k)=q k)
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T)
    (hs : ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState w z.1 z.2) :
    ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T),
      nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T v) z.1 z.2 =
        nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T w) z.1 z.2 := by
  have hm : Measurable (Prod.map
      (id : AnisotropicObservationState n → AnisotropicObservationState n)
      (observationRefinementProject (E := AnisotropicObservationState n) (S := Configuration n) d T)) :=
    measurable_id.prodMap (measurable_observationRefinementProject d T)
  rw [←anisotropicRecordedProfileTreeLaw_refinement D μ a q Q d hQ hl T] at hs
  have h := ae_of_ae_map hm.aemeasurable hs
  filter_upwards [h] with z hz
  change nativeStreamingVertexState v z.1 (observationRefinementProject d T z.2) =
    nativeStreamingVertexState w z.1 (observationRefinementProject d T z.2) at hz
  simpa only [nativeStreamingRefinementVertexEmbed_state] using hz

theorem nativeStreamingEdgeVertexPairProbability_eq_of_clock_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (f : NativeStreamingEdge T) (r : Paper.Overlap)
    (hr : r ∈ Icc (q (f.depth+1)) (q f.depth))
    (v w : FiniteCascadeRecordVertex T) (hc : q v.depth=q w.depth)
    (hs : ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState w z.1 z.2) :
    nativeStreamingEdgeVertexPairProbability D μ a q T f v r =
      nativeStreamingEdgeVertexPairProbability D μ a q T f w r := by
  let d := nativeStreamingEdgeSubdivision f.depth
  let Q := nativeStreamingEdgeSchedule q f.depth r
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq f.depth r hr
  have hl : ∀ k, Q (observationRefinementDepth d k)=q k :=
    nativeStreamingEdgeSchedule_refinement q f.depth r
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hl 0).trans hzero
  have hc' : Q (nativeStreamingRefinementVertexEmbed d T v).depth =
      Q (nativeStreamingRefinementVertexEmbed d T w).depth := by
    rw [nativeStreamingRefinementVertexEmbed_depth,nativeStreamingRefinementVertexEmbed_depth,
      hl,hl,hc]
  have hs' := nativeStreamingRefinement_ae_state_eq D μ a q Q d hQ hl T v w hs
  have hp := nativeStreamingCrossVertexProbability_right_eq_of_clock_state D μ a Q hQ hQ0
    (observationRefineTree d T) (nativeStreamingRefinementVertexEmbed d T v)
    (nativeStreamingRefinementVertexEmbed d T w) (nativeStreamingEdgeRefinedVertex d f) hc' hs'
  exact congrArg (fun P => P.map
    (fun z => ((z.1.1,observationRefinementProject d T z.1.2),z.2))) hp

theorem nativeStreamingPatternMoment_cross_valid_edge_same_time_left
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth)
    (o : NativeStreamingOrigin T) (ho : nativeCoalescedOriginValid q o) :
    nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeParentVertex e)) o) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeChildVertex e)) o) := by
  cases o with
  | vertex w =>
      exact nativeStreamingPatternMoment_cross_vertex_edge_same_time_left D μ a q hq hzero T F e he w
  | edge f r =>
      have hc : q (nativeStreamingEdgeParentVertex e).depth =
          q (nativeStreamingEdgeChildVertex e).depth := by
        rw [nativeStreamingEdgeParentVertex_depth,nativeStreamingEdgeChildVertex_depth,he]
      have hp := nativeStreamingEdgeVertexPairProbability_eq_of_clock_state D μ a q hq hzero
        T f r ho (nativeStreamingEdgeParentVertex e) (nativeStreamingEdgeChildVertex e) hc
        (nativeStreamingRecordedLaw_edge_same_time_coherent D μ a q T e he)
      simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability]
      rw [hp,nativeStreamingOriginCommonClock_vertex_edge_same_time q e he f r ho]

theorem nativeStreamingPatternMoment_cross_valid_edge_same_time_right
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth)
    (o : NativeStreamingOrigin T) (ho : nativeCoalescedOriginValid q o) :
    nativeStreamingPatternMoment D μ a q T F
        (.cross o (.vertex (nativeStreamingEdgeParentVertex e))) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross o (.vertex (nativeStreamingEdgeChildVertex e))) := by
  cases o with
  | vertex v =>
      exact nativeStreamingPatternMoment_cross_vertex_edge_same_time_right D μ a q hq hzero T F e he v
  | edge f r =>
      have hc : q (nativeStreamingEdgeParentVertex e).depth =
          q (nativeStreamingEdgeChildVertex e).depth := by
        rw [nativeStreamingEdgeParentVertex_depth,nativeStreamingEdgeChildVertex_depth,he]
      have hp := nativeStreamingEdgeVertexPairProbability_eq_of_clock_state D μ a q hq hzero
        T f r ho (nativeStreamingEdgeParentVertex e) (nativeStreamingEdgeChildVertex e) hc
        (nativeStreamingRecordedLaw_edge_same_time_coherent D μ a q T e he)
      simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability]
      rw [hp]
      have hclock := nativeStreamingOriginCommonClock_vertex_edge_same_time q e he f r ho
      exact congrArg (fun t => nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgeVertexPairProbability D μ a q T f
          (nativeStreamingEdgeChildVertex e) r) (nativeStreamingDefectSpinTest T F t)) hclock

theorem nativeStreamingPatternMoment_cross_valid_upper_left
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (o : NativeStreamingOrigin T)
    (ho : nativeCoalescedOriginValid q o) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.edge e (q e.depth)) o) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeChildVertex e)) o) := by
  cases o with
  | vertex w => exact nativeStreamingPatternMoment_cross_edge_child_endpoint D μ a q hq hzero T F e w
  | edge f r => exact nativeStreamingPatternMoment_cross_left_child_endpoint D μ a q hq hzero T F e f r ho

theorem nativeStreamingPatternMoment_cross_valid_upper_right
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (o : NativeStreamingOrigin T)
    (ho : nativeCoalescedOriginValid q o) :
    nativeStreamingPatternMoment D μ a q T F (.cross o (.edge e (q e.depth))) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross o (.vertex (nativeStreamingEdgeChildVertex e))) := by
  cases o with
  | vertex v => exact nativeStreamingPatternMoment_cross_child_endpoint_edge D μ a q hq hzero T F v e
  | edge f r => exact nativeStreamingPatternMoment_cross_right_child_endpoint D μ a q hq hzero T F f e r ho

end QuantitativeFollowup
