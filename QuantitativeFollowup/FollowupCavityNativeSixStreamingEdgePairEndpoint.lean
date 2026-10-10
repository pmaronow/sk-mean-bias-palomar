module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairProbabilityPhysical
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMoments

@[expose] public section

/-! At two genuine child-endpoint clocks, the complete edge/edge marked
law equals the old-vertex/old-vertex law. The two fresh terminal draws
remain conditionally independent even when the clocks or edges coincide. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem edgePairEndpoint_cross_law_state_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w V W : FiniteCascadeRecordVertex T)
    (hv : q v.depth=q V.depth) (hw : q w.depth=q W.depth)
    (hs : ∀ᵐz∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState V z.1 z.2 ∧
      nativeStreamingVertexState w z.1 z.2=nativeStreamingVertexState W z.1 z.2) :
    nativeStreamingCrossVertexLaw D μ a q T v w =
      nativeStreamingCrossVertexLaw D μ a q T V W := by
  apply Measure.compProd_congr
  filter_upwards [hs] with z hz
  simp only [nativeStreamingCrossVertexKernel,nativeStreamingSingleVertexKernel,
    Kernel.prod_apply,Kernel.comap_apply,Function.uncurry_def,hv,hw,hz.1,hz.2]

theorem nativeStreamingEdgePairProbability_child_endpoints
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T) :
    nativeStreamingEdgePairProbability D μ a q T e f (q e.depth) (q f.depth) =
      nativeStreamingCrossVertexProbability D μ a q T
        (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f) := by
  let d := nativeStreamingPairObservationSubdivision
  let Q := nativeStreamingPairObservationSchedule q e.depth f.depth (q e.depth) (q f.depth)
  let p := nativeStreamingPairObservationIndex e.depth f.depth (q e.depth) (q f.depth)
  let k := nativeStreamingPairObservationIndex f.depth e.depth (q f.depth) (q e.depth)
  have hp : p<d e.depth := nativeStreamingPairObservationIndex_lt _ _ _ _
  have hk : k<d f.depth := nativeStreamingPairObservationIndex_lt _ _ _ _
  have hr : q (e.depth+1)≤q e.depth ∧ q e.depth≤q e.depth :=
    ⟨hq (Nat.le_succ _),le_rfl⟩
  have hl : q (f.depth+1)≤q f.depth ∧ q f.depth≤q f.depth :=
    ⟨hq (Nat.le_succ _),le_rfl⟩
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq
    e.depth f.depth (q e.depth) (q f.depth) hr hl
  have hlevels : ∀j, Q (observationRefinementDepth d j)=q j :=
    nativeStreamingPairObservationSchedule_refinement q e.depth f.depth (q e.depth) (q f.depth)
  have hQ0 : Q 0=1 := by
    simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hpr : Q (observationRefinementDepth d e.depth+p+1)=q e.depth :=
    nativeStreamingPairObservationIndex_level q e.depth f.depth (q e.depth) (q f.depth)
  have hkl : Q (observationRefinementDepth d f.depth+k+1)=q f.depth :=
    nativeStreamingPairObservationIndex_second_level q e.depth f.depth (q e.depth) (q f.depth)
  have hv : Q (nativeStreamingEdgeSelectedVertex d e p).depth =
      Q (nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeChildVertex e)).depth := by
    rw [nativeStreamingEdgeSelectedVertex_depth d e p hp,hpr,
      nativeStreamingRefinementVertexEmbed_depth,hlevels,nativeStreamingEdgeChildVertex_depth]
  have hw : Q (nativeStreamingEdgeSelectedVertex d f k).depth =
      Q (nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeChildVertex f)).depth := by
    rw [nativeStreamingEdgeSelectedVertex_depth d f k hk,hkl,
      nativeStreamingRefinementVertexEmbed_depth,hlevels,nativeStreamingEdgeChildVertex_depth]
  have hs : ∀ᵐz∂anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T),
      nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d e p) z.1 z.2 =
        nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T
          (nativeStreamingEdgeChildVertex e)) z.1 z.2 ∧
      nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d f k) z.1 z.2 =
        nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T
          (nativeStreamingEdgeChildVertex f)) z.1 z.2 := by
    apply Measure.ae_compProd_of_ae_ae
      ((measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
        (nativeStreamingVertexState_measurable _)).inter
        (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
          (nativeStreamingVertexState_measurable _)))
    apply Eventually.of_forall
    intro x
    exact (nativeStreamingSelected_child_endpoint_state D μ q Q d hq hQ hlevels T e p hp hpr x).and
      (nativeStreamingSelected_child_endpoint_state D μ q Q d hq hQ hlevels T f k hk hkl x)
  have he := edgePairEndpoint_cross_law_state_eq D μ a Q (observationRefineTree d T)
    _ _ _ _ hv hw hs
  have H := nativeStreamingCrossVertexLaw_refinement D μ a q Q d hQ hlevels T
    (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
  rw [←he,←nativeStreamingCrossVertexProbability_eq_law D μ a Q hQ hQ0,
    ←nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero] at H
  apply ProbabilityMeasure.toMeasure_injective
  simpa only [nativeStreamingEdgePairProbability,nativeStreamingEdgePairProbabilityFixed,
    ProbabilityMeasure.toMeasure_map,d,Q,p,k] using H

theorem nativeStreamingPatternMoment_cross_edge_child_endpoints
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e f : NativeStreamingEdge T) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.edge e (q e.depth)) (.edge f (q f.depth))) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeChildVertex e)) (.vertex (nativeStreamingEdgeChildVertex f))) := by
  have hc : nativeStreamingOriginCommonClock q T (.edge e (q e.depth)) (.edge f (q f.depth)) =
      nativeStreamingOriginCommonClock q T (.vertex (nativeStreamingEdgeChildVertex e))
        (.vertex (nativeStreamingEdgeChildVertex f)) := by
    simp only [nativeStreamingOriginCommonClock]
    unfold nativeStreamingSelectedCommonClock
    split_ifs <;> simp_all only [min_self]
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,hc,
    nativeStreamingEdgePairProbability_child_endpoints D μ a q hq hzero T e f]

end QuantitativeFollowup
