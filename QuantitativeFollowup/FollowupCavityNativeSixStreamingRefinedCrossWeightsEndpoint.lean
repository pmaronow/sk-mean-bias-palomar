module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedCrossPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairEndpoint

@[expose] public section

/-! A single child-endpoint mark collapses in the genuine two-edge law,
while the other mark remains at its actual clock. Both terminal draws
remain independent conditional on the selected states, including equal
edges and equal clocks. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem refinedCrossEndpoint_cross_law_state_eq
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

theorem nativeStreamingEdgePairProbability_right_child_endpoint
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (r : Paper.Overlap) (hr : q (e.depth+1)≤r ∧ r≤q e.depth) :
    nativeStreamingEdgePairProbability D μ a q T e f r (q f.depth) =
      nativeStreamingOriginCrossProbability D μ a q T
        (.edge e r) (.vertex (nativeStreamingEdgeChildVertex f)) := by
  let d := nativeStreamingPairObservationSubdivision
  let Q := nativeStreamingPairObservationSchedule q e.depth f.depth r (q f.depth)
  let p := nativeStreamingPairObservationIndex e.depth f.depth r (q f.depth)
  let k := nativeStreamingPairObservationIndex f.depth e.depth (q f.depth) r
  have hp : p<d e.depth := nativeStreamingPairObservationIndex_lt _ _ _ _
  have hk : k<d f.depth := nativeStreamingPairObservationIndex_lt _ _ _ _
  have hl : q (f.depth+1)≤q f.depth ∧ q f.depth≤q f.depth :=
    ⟨hq (Nat.le_succ _),le_rfl⟩
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq
    e.depth f.depth r (q f.depth) hr hl
  have hlevels : ∀j, Q (observationRefinementDepth d j)=q j :=
    nativeStreamingPairObservationSchedule_refinement q e.depth f.depth r (q f.depth)
  have hQ0 : Q 0=1 := by
    simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hpr : Q (observationRefinementDepth d e.depth+p+1)=r :=
    nativeStreamingPairObservationIndex_level q e.depth f.depth r (q f.depth)
  have hkl : Q (observationRefinementDepth d f.depth+k+1)=q f.depth :=
    nativeStreamingPairObservationIndex_second_level q e.depth f.depth r (q f.depth)
  have hw : Q (nativeStreamingEdgeSelectedVertex d f k).depth =
      Q (nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeChildVertex f)).depth := by
    rw [nativeStreamingEdgeSelectedVertex_depth d f k hk,hkl,
      nativeStreamingRefinementVertexEmbed_depth,hlevels,nativeStreamingEdgeChildVertex_depth]
  have hs : ∀ᵐz∂anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T),
      nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d f k) z.1 z.2 =
        nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T
          (nativeStreamingEdgeChildVertex f)) z.1 z.2 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
        (nativeStreamingVertexState_measurable _))
    exact Eventually.of_forall fun x =>
      nativeStreamingSelected_child_endpoint_state D μ q Q d hq hQ hlevels T f k hk hkl x
  have he := refinedCrossEndpoint_cross_law_state_eq D μ a Q (observationRefineTree d T)
    (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)
    (nativeStreamingEdgeSelectedVertex d e p)
    (nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeChildVertex f))
    rfl hw (hs.mono fun z hz => ⟨rfl,hz⟩)
  have H := nativeStreamingSelectedCrossLaw_EV_projection_eq_origin D μ a q Q d hQ hlevels hzero
    T e p hp (nativeStreamingEdgeChildVertex f)
  rw [←he,←nativeStreamingCrossVertexProbability_eq_law D μ a Q hQ hQ0,hpr] at H
  apply ProbabilityMeasure.toMeasure_injective
  simpa only [nativeStreamingEdgePairProbability,nativeStreamingEdgePairProbabilityFixed,
    ProbabilityMeasure.toMeasure_map,d,Q,p,k] using H

theorem nativeStreamingEdgePairProbability_left_child_endpoint
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (l : Paper.Overlap) (hl : q (f.depth+1)≤l ∧ l≤q f.depth) :
    nativeStreamingEdgePairProbability D μ a q T e f (q e.depth) l =
      nativeStreamingOriginCrossProbability D μ a q T
        (.vertex (nativeStreamingEdgeChildVertex e)) (.edge f l) := by
  let d := nativeStreamingPairObservationSubdivision
  let Q := nativeStreamingPairObservationSchedule q e.depth f.depth (q e.depth) l
  let p := nativeStreamingPairObservationIndex e.depth f.depth (q e.depth) l
  let k := nativeStreamingPairObservationIndex f.depth e.depth l (q e.depth)
  have hp : p<d e.depth := nativeStreamingPairObservationIndex_lt _ _ _ _
  have hk : k<d f.depth := nativeStreamingPairObservationIndex_lt _ _ _ _
  have hr : q (e.depth+1)≤q e.depth ∧ q e.depth≤q e.depth :=
    ⟨hq (Nat.le_succ _),le_rfl⟩
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq
    e.depth f.depth (q e.depth) l hr hl
  have hlevels : ∀j, Q (observationRefinementDepth d j)=q j :=
    nativeStreamingPairObservationSchedule_refinement q e.depth f.depth (q e.depth) l
  have hQ0 : Q 0=1 := by
    simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hpr : Q (observationRefinementDepth d e.depth+p+1)=q e.depth :=
    nativeStreamingPairObservationIndex_level q e.depth f.depth (q e.depth) l
  have hkl : Q (observationRefinementDepth d f.depth+k+1)=l :=
    nativeStreamingPairObservationIndex_second_level q e.depth f.depth (q e.depth) l
  have hv : Q (nativeStreamingEdgeSelectedVertex d e p).depth =
      Q (nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeChildVertex e)).depth := by
    rw [nativeStreamingEdgeSelectedVertex_depth d e p hp,hpr,
      nativeStreamingRefinementVertexEmbed_depth,hlevels,nativeStreamingEdgeChildVertex_depth]
  have hs : ∀ᵐz∂anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T),
      nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d e p) z.1 z.2 =
        nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T
          (nativeStreamingEdgeChildVertex e)) z.1 z.2 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
        (nativeStreamingVertexState_measurable _))
    exact Eventually.of_forall fun x =>
      nativeStreamingSelected_child_endpoint_state D μ q Q d hq hQ hlevels T e p hp hpr x
  have he := refinedCrossEndpoint_cross_law_state_eq D μ a Q (observationRefineTree d T)
    (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)
    (nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeChildVertex e))
    (nativeStreamingEdgeSelectedVertex d f k)
    hv rfl (hs.mono fun z hz => ⟨hz,rfl⟩)
  have H := nativeStreamingSelectedCrossLaw_VE_projection_eq_origin D μ a q Q d hQ hlevels hzero
    T f k hk (nativeStreamingEdgeChildVertex e)
  rw [←he,←nativeStreamingCrossVertexProbability_eq_law D μ a Q hQ hQ0,hkl] at H
  apply ProbabilityMeasure.toMeasure_injective
  simpa only [nativeStreamingEdgePairProbability,nativeStreamingEdgePairProbabilityFixed,
    ProbabilityMeasure.toMeasure_map,d,Q,p,k] using H

theorem nativeStreamingPatternMoment_cross_right_child_endpoint
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e f : NativeStreamingEdge T) (r : Paper.Overlap)
    (hr : q (e.depth+1)≤r ∧ r≤q e.depth) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.edge f (q f.depth))) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.edge e r) (.vertex (nativeStreamingEdgeChildVertex f))) := by
  have hc : nativeStreamingOriginCommonClock q T (.edge e r) (.edge f (q f.depth)) =
      nativeStreamingOriginCommonClock q T (.edge e r) (.vertex (nativeStreamingEdgeChildVertex f)) := by
    simp only [nativeStreamingOriginCommonClock,
      nativeStreamingSelectedGeometry_commonPathDepth_symm T (nativeStreamingEdgeChildVertex f)
        (nativeStreamingEdgeChildVertex e)]
    unfold nativeStreamingSelectedCommonClock nativeStreamingOldSelectedCommonClock
    split_ifs <;> simp_all only [min_eq_left hr.2]
  simp only [nativeStreamingPatternMoment]
  rw [hc]
  exact congrArg (fun P => nativeStreamingTerminalMarkMoment P
    (nativeStreamingDefectSpinTest T F (nativeStreamingOriginCommonClock q T
      (.edge e r) (.vertex (nativeStreamingEdgeChildVertex f)))))
    (nativeStreamingEdgePairProbability_right_child_endpoint D μ a q hq hzero T e f r hr)

theorem nativeStreamingPatternMoment_cross_left_child_endpoint
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e f : NativeStreamingEdge T) (l : Paper.Overlap)
    (hl : q (f.depth+1)≤l ∧ l≤q f.depth) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.edge e (q e.depth)) (.edge f l)) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeChildVertex e)) (.edge f l)) := by
  have hc : nativeStreamingOriginCommonClock q T (.edge e (q e.depth)) (.edge f l) =
      nativeStreamingOriginCommonClock q T (.vertex (nativeStreamingEdgeChildVertex e)) (.edge f l) := by
    simp only [nativeStreamingOriginCommonClock]
    unfold nativeStreamingSelectedCommonClock nativeStreamingOldSelectedCommonClock
    split_ifs <;> simp_all only [min_eq_right]
  simp only [nativeStreamingPatternMoment]
  rw [hc]
  exact congrArg (fun P => nativeStreamingTerminalMarkMoment P
    (nativeStreamingDefectSpinTest T F (nativeStreamingOriginCommonClock q T
      (.vertex (nativeStreamingEdgeChildVertex e)) (.edge f l))))
    (nativeStreamingEdgePairProbability_left_child_endpoint D μ a q hq hzero T e f l hl)

end QuantitativeFollowup
