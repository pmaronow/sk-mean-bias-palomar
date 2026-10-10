module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeEndpointCoherenceLaws
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexPairContinuity

@[expose] public section

/-! A genuine two-location marked law at an inserted edge endpoint.
The edge mark and arbitrary old-vertex mark stay conditionally independent,
and the complete old record is projected by the actual refinement law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingCrossVertexLaw_refinement
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j, Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v)
      (nativeStreamingRefinementVertexEmbed d T w)).map
      (fun z => ((z.1.1,observationRefinementProject d T z.1.2),z.2)) =
      nativeStreamingCrossVertexLaw D μ a q T v w := by
  have hk : nativeStreamingCrossVertexKernel D μ Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v)
      (nativeStreamingRefinementVertexEmbed d T w) =
      (nativeStreamingCrossVertexKernel D μ q T v w).comap
        (Prod.map id (observationRefinementProject d T))
        (measurable_id.prodMap (measurable_observationRefinementProject d T)) := by
    unfold nativeStreamingCrossVertexKernel
    rw [nativeStreamingSingleVertexKernel_refinement D μ q Q d hlevels T v,
      nativeStreamingSingleVertexKernel_refinement D μ q Q d hlevels T w]
    exact (Kernel.comap_prod _ _ _).symm
  unfold nativeStreamingCrossVertexLaw
  rw [hk]
  have he := compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (observationRefinementProject d T))
    (measurable_id.prodMap (measurable_observationRefinementProject d T))
    (nativeStreamingCrossVertexKernel D μ q T v w)
  rw [anisotropicRecordedProfileTreeLaw_refinement D μ a q Q d hQ hlevels T] at he
  exact he

private theorem cross_mark_law_first_state_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w t : FiniteCascadeRecordVertex T) (hc : q v.depth=q w.depth)
    (hs : ∀ᵐz∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState w z.1 z.2) :
    nativeStreamingCrossVertexLaw D μ a q T v t =
      nativeStreamingCrossVertexLaw D μ a q T w t := by
  have hk : nativeStreamingCrossVertexKernel D μ q T v t =ᵐ[
      anisotropicRecordedProfileTreeLaw D μ a q T]
        nativeStreamingCrossVertexKernel D μ q T w t := by
    filter_upwards [hs] with z hz
    change (nativeStreamingSingleVertexKernel D μ q T v ×ₖ
      nativeStreamingSingleVertexKernel D μ q T t) z =
      (nativeStreamingSingleVertexKernel D μ q T w ×ₖ
        nativeStreamingSingleVertexKernel D μ q T t) z
    rw [Kernel.prod_apply, Kernel.prod_apply]
    change (anisotropicObservationTerminalSpinKernel D μ (q v.depth)
      (nativeStreamingVertexState v z.1 z.2)).prod
        (anisotropicObservationTerminalSpinKernel D μ (q t.depth)
          (nativeStreamingVertexState t z.1 z.2)) =
      (anisotropicObservationTerminalSpinKernel D μ (q w.depth)
        (nativeStreamingVertexState w z.1 z.2)).prod
          (anisotropicObservationTerminalSpinKernel D μ (q t.depth)
            (nativeStreamingVertexState t z.1 z.2))
    rw [hc,hz]
  exact Measure.compProd_congr hk

theorem nativeStreamingEdgeVertexPairProbability_endpoint
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (v : FiniteCascadeRecordVertex T) (b : Bool) :
    nativeStreamingEdgeVertexPairProbability D μ a q T e v
      (q (nativeStreamingEndpointVertex e b).depth) =
      nativeStreamingCrossVertexProbability D μ a q T
        (nativeStreamingEndpointVertex e b) v := by
  let w := nativeStreamingEndpointVertex e b
  let r := q w.depth
  let d := nativeStreamingEdgeSubdivision e.depth
  let Q := nativeStreamingEdgeSchedule q e.depth r
  let R := observationRefineTree d T
  let s := nativeStreamingEdgeRefinedVertex d e
  let W := nativeStreamingRefinementVertexEmbed d T w
  let V := nativeStreamingRefinementVertexEmbed d T v
  have hrr : q (e.depth+1)≤r ∧ r≤q e.depth := by
    cases b
    · simpa only [r,w,nativeStreamingEndpointVertex,nativeStreamingEdgeChildVertex_depth]
        using And.intro (hq (Nat.le_succ e.depth)) (le_rfl : q e.depth≤q e.depth)
    · simpa only [r,w,nativeStreamingEndpointVertex,nativeStreamingEdgeParentVertex_depth]
        using And.intro (le_rfl : q (e.depth+1)≤q (e.depth+1)) (hq (Nat.le_succ e.depth))
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hrr
  have hQ0 : Q 0=1 := by simpa [Q,nativeStreamingEdgeSchedule] using hzero
  have hc : Q s.depth=Q W.depth := by
    dsimp only [Q,s,W,d]
    rw [nativeStreamingEdgeRefinedVertex_inserted_level,nativeStreamingRefinementVertexEmbed_depth,
      nativeStreamingEdgeSchedule_refinement]
  have hs : ∀ᵐz∂anisotropicRecordedProfileTreeLaw D μ a Q R,
      nativeStreamingVertexState s z.1 z.2=nativeStreamingVertexState W z.1 z.2 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun (nativeStreamingVertexState_measurable s)
        (nativeStreamingVertexState_measurable W))
    cases b
    · apply Eventually.of_forall
      intro x
      simpa only [Q,R,s,W,d,r,w,nativeStreamingEndpointVertex,
        nativeStreamingEdgeChildVertex_depth,Function.uncurry_def] using
        nativeStreamingInserted_child_endpoint_state D μ q e x
    · apply Eventually.of_forall
      intro x
      simpa only [Q,R,s,W,d,r,w,nativeStreamingEndpointVertex,
        nativeStreamingEdgeParentVertex_depth,Function.uncurry_def] using
        nativeStreamingInserted_parent_endpoint_state D μ q e x
  have H := cross_mark_law_first_state_eq D μ a Q R s W V hc hs
  apply ProbabilityMeasure.toMeasure_injective
  have hh := nativeStreamingCrossVertexLaw_refinement D μ a q Q d hQ
    (nativeStreamingEdgeSchedule_refinement q e.depth r) T w v
  rw [←H, ←nativeStreamingCrossVertexProbability_eq_law D μ a Q hQ hQ0 R s V,
    ←nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero T w v] at hh
  simpa only [nativeStreamingEdgeVertexPairProbability,w,r,d,Q,R,s,V,
    ProbabilityMeasure.toMeasure_map] using hh

end QuantitativeFollowup
