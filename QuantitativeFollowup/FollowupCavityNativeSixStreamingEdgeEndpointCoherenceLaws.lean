module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeEndpointCoherence

@[expose] public section

/-! The actual single- and two-fresh-spin probability laws at both inserted
edge endpoints, with the complete original record retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem endpoint_mark_laws_state_eq
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (a:ℝ)
    (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (v w:FiniteCascadeRecordVertex T) (hclock:q v.depth=q w.depth)
    (hs:∀ᵐz∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState w z.1 z.2) :
    nativeStreamingSingleVertexLaw D μ a q T v=nativeStreamingSingleVertexLaw D μ a q T w ∧
      nativeStreamingCurrentPairLaw D μ a q T v=nativeStreamingCurrentPairLaw D μ a q T w := by
  have hsingle:nativeStreamingSingleVertexKernel D μ q T v =ᵐ[
      anisotropicRecordedProfileTreeLaw D μ a q T]
        nativeStreamingSingleVertexKernel D μ q T w := by
    filter_upwards [hs] with z hz
    change anisotropicObservationTerminalSpinKernel D μ (q v.depth)
      (nativeStreamingVertexState v z.1 z.2)=
        anisotropicObservationTerminalSpinKernel D μ (q w.depth)
          (nativeStreamingVertexState w z.1 z.2)
    rw [hclock,hz]
  have hpair:nativeStreamingCurrentPairKernel D μ q T v =ᵐ[
      anisotropicRecordedProfileTreeLaw D μ a q T]
        nativeStreamingCurrentPairKernel D μ q T w := by
    filter_upwards [hs] with z hz
    change (anisotropicObservationTerminalSpinKernel D μ (q v.depth) ×ₖ
      anisotropicObservationTerminalSpinKernel D μ (q v.depth))
        (nativeStreamingVertexState v z.1 z.2)=
      (anisotropicObservationTerminalSpinKernel D μ (q w.depth) ×ₖ
        anisotropicObservationTerminalSpinKernel D μ (q w.depth))
          (nativeStreamingVertexState w z.1 z.2)
    rw [hclock,hz]
  haveI:=nativeStreamingSingleVertexKernel_markov D μ q T v
  haveI:=nativeStreamingSingleVertexKernel_markov D μ q T w
  exact ⟨Measure.compProd_congr hsingle,Measure.compProd_congr hpair⟩

theorem nativeStreamingCurrentPairLaw_refinement (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q Q:ℕ→Paper.Overlap) (d:ℕ→ℕ)
    (hQ:Antitone Q) (hlevels:∀j,Q (observationRefinementDepth d j)=q j)
    (T:FiniteTerminalGenealogy J) (v:FiniteCascadeRecordVertex T) :
    (nativeStreamingCurrentPairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v)).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      nativeStreamingCurrentPairLaw D μ a q T v := by
  have hk:nativeStreamingCurrentPairKernel D μ Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v)=
      (nativeStreamingCurrentPairKernel D μ q T v).comap
        (Prod.map id (observationRefinementProject d T))
        (measurable_id.prodMap (measurable_observationRefinementProject d T)) := by
    ext z σ hs
    change ((anisotropicObservationTerminalSpinKernel D μ
      (Q (nativeStreamingRefinementVertexEmbed d T v).depth) ×ₖ
      anisotropicObservationTerminalSpinKernel D μ
        (Q (nativeStreamingRefinementVertexEmbed d T v).depth))
          (nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T v) z.1 z.2)) σ=_
    rw [nativeStreamingRefinementVertexEmbed_depth,hlevels,nativeStreamingRefinementVertexEmbed_state]
    rfl
  unfold nativeStreamingCurrentPairLaw
  rw [hk]
  have he:=compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (observationRefinementProject d T))
    (measurable_id.prodMap (measurable_observationRefinementProject d T))
    (nativeStreamingCurrentPairKernel D μ q T v)
  rw [anisotropicRecordedProfileTreeLaw_refinement D μ a q Q d hQ hlevels T] at he
  exact he

@[reducible] def nativeStreamingEndpointVertex {j:ℕ} {T:FiniteTerminalGenealogy j}
    (e:NativeStreamingEdge T) : Bool→FiniteCascadeRecordVertex T
  | false => nativeStreamingEdgeChildVertex e
  | true => nativeStreamingEdgeParentVertex e

theorem nativeStreamingEdgeMarkProbabilities_endpoint
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (a:ℝ)
    (q:ℕ→Paper.Overlap) (hq:Antitone q) (hzero:q 0=1)
    (T:FiniteTerminalGenealogy J) (e:NativeStreamingEdge T) (b:Bool) :
    nativeStreamingEdgeSingleMarkProbability D μ a q T e (q (nativeStreamingEndpointVertex e b).depth)=
      nativeStreamingSingleVertexProbability D μ a q T (nativeStreamingEndpointVertex e b) ∧
    nativeStreamingEdgeCurrentPairProbability D μ a q T e (q (nativeStreamingEndpointVertex e b).depth)=
      nativeStreamingCurrentPairProbability D μ a q T (nativeStreamingEndpointVertex e b) := by
  let v:=nativeStreamingEndpointVertex e b
  let r:=q v.depth
  let d:=nativeStreamingEdgeSubdivision e.depth
  let Q:=nativeStreamingEdgeSchedule q e.depth r
  let R:=observationRefineTree d T
  let s:=nativeStreamingEdgeRefinedVertex d e
  let w:=nativeStreamingRefinementVertexEmbed d T v
  have hrr:q (e.depth+1)≤r ∧ r≤q e.depth:=by
    cases b
    · simpa only [r,v,nativeStreamingEndpointVertex,nativeStreamingEdgeChildVertex_depth]
        using And.intro (hq (Nat.le_succ e.depth)) (le_rfl : q e.depth≤q e.depth)
    · simpa only [r,v,nativeStreamingEndpointVertex,nativeStreamingEdgeParentVertex_depth]
        using And.intro (le_rfl : q (e.depth+1)≤q (e.depth+1)) (hq (Nat.le_succ e.depth))
  have hQ:Antitone Q:=nativeStreamingEdgeSchedule_antitone q hq e.depth r hrr
  have hQ0:Q 0=1:=by simpa [Q,nativeStreamingEdgeSchedule] using hzero
  have hclock:Q s.depth=Q w.depth:=by
    dsimp only [Q,s,w,d]
    rw [nativeStreamingEdgeRefinedVertex_inserted_level,nativeStreamingRefinementVertexEmbed_depth,
      nativeStreamingEdgeSchedule_refinement]
  have hs:∀ᵐz∂anisotropicRecordedProfileTreeLaw D μ a Q R,
      nativeStreamingVertexState s z.1 z.2=nativeStreamingVertexState w z.1 z.2:=by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun (nativeStreamingVertexState_measurable s)
        (nativeStreamingVertexState_measurable w))
    cases b
    · apply Eventually.of_forall
      intro x
      simpa only [Q,R,s,w,d,r,v,nativeStreamingEndpointVertex,
        nativeStreamingEdgeChildVertex_depth,Function.uncurry_def] using
        nativeStreamingInserted_child_endpoint_state D μ q e x
    · apply Eventually.of_forall
      intro x
      simpa only [Q,R,s,w,d,r,v,nativeStreamingEndpointVertex,
        nativeStreamingEdgeParentVertex_depth,Function.uncurry_def] using
        nativeStreamingInserted_parent_endpoint_state D μ q e x
  have H:=endpoint_mark_laws_state_eq D μ a Q R s w hclock hs
  constructor
  · apply ProbabilityMeasure.toMeasure_injective
    have hh := nativeStreamingSingleVertexLaw_refinement D μ a q Q d hQ
      (nativeStreamingEdgeSchedule_refinement q e.depth r) T v
    rw [←H.1, ←nativeStreamingSingleVertexProbability_eq_law D μ a Q hQ hQ0 R s,
      ←nativeStreamingSingleVertexProbability_eq_law D μ a q hq hzero T v] at hh
    simpa only [nativeStreamingEdgeSingleMarkProbability, v,r,d,Q,R,s,
      ProbabilityMeasure.toMeasure_map] using hh
  · apply ProbabilityMeasure.toMeasure_injective
    have hh := nativeStreamingCurrentPairLaw_refinement D μ a q Q d hQ
      (nativeStreamingEdgeSchedule_refinement q e.depth r) T v
    rw [←H.2, ←nativeStreamingCurrentPairProbability_eq_law D μ a Q hQ hQ0 R s,
      ←nativeStreamingCurrentPairProbability_eq_law D μ a q hq hzero T v] at hh
    simpa only [nativeStreamingEdgeCurrentPairProbability, v,r,d,Q,R,s,
      ProbabilityMeasure.toMeasure_map] using hh

end QuantitativeFollowup
