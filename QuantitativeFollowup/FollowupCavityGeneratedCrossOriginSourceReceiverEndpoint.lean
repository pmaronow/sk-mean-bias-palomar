module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverObserved
public import QuantitativeFollowup.SupportingGeneratedEndpointEdgeVertexState

@[expose] public section

/-! Endpoint padding transports both independent fresh marks together
with the hidden ancestral observation and every original record. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem printedGeneratedEndpointEdgeVertexProbability_project
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (e : NativeStreamingEdge U.tree) (v : FiniteCascadeRecordVertex U.tree) (r : Paper.Overlap)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth) :
    (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedEndpointClock U h)
      (nativeStreamingGeneratedEndpointComponent U).tree (.edge (printedGeneratedEndpointEdge U e) r)
        (.vertex (nativeStreamingGeneratedEndpointVertex U v)) : Measure _).map
      (printedGeneratedEndpointCrossRecordProject (E := AnisotropicObservationState n)
        (S := Configuration n) U) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (.edge e r) (.vertex v) : Measure _) := by
  let V := nativeStreamingGeneratedEndpointComponent U
  let q := nativeStreamingGeneratedComponentClock U h
  let Q := nativeStreamingGeneratedEndpointClock U h
  let π : (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) V.tree)) →
      (AnisotropicObservationState n × (AnisotropicObservationState n ×
        Records (AnisotropicObservationState n) (Configuration n) U.tree)) :=
    Prod.map id (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U))
  have hπ : Measurable π :=
    measurable_id.prodMap (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject U))
  let L := anisotropicObservationInitialLaw D μ a ⊗ₘ
    nativeStreamingEdgeObservedKernel D μ Q V.tree (printedGeneratedEndpointEdge U e) r
  have hQ : Antitone Q := by
    simpa only [Q,V,nativeStreamingGeneratedEndpointComponent_clock] using
      nativeStreamingGeneratedComponentClock_antitone V h
  have hQ0 : Q 0=1 := by
    simpa only [Q,V,nativeStreamingGeneratedEndpointComponent_clock] using
      nativeStreamingGeneratedComponentClock_terminal V h
  have hcell := printedGeneratedEndpointEdge_cell U e h r hr
  simp only [nativeStreamingGeneratedEndpointComponent_clock] at hcell
  have hk : printedGeneratedEdgeVertexObservedSpinKernel D μ Q V.tree
      (nativeStreamingGeneratedEndpointVertex U v) r =ᵐ[L]
      (printedGeneratedEdgeVertexObservedSpinKernel D μ q U.tree v r).comap π hπ := by
    filter_upwards [printedGeneratedEndpoint_edge_vertex_state D μ a U h e r hr v] with z hz
    change nativeStreamingVertexState (nativeStreamingGeneratedEndpointVertex U v) z.1 z.2.2 =
      nativeStreamingVertexState v z.1 (nativeStreamingGeneratedEndpointRecordProject U z.2.2) at hz
    change nativeStreamingVertexState (nativeStreamingGeneratedEndpointVertex U v) z.1 z.2.2 =
      nativeStreamingVertexState v z.1 (nativeStreamingGeneratedEndpointRecordProject U z.2.2) at hz
    simp only [printedGeneratedEdgeVertexObservedSpinKernel,Kernel.prod_apply,Kernel.comap_apply,
      nativeStreamingEdgeObservedSpinKernel,nativeStreamingSingleVertexKernel]
    change (anisotropicObservationTerminalSpinKernel D μ r z.2.1).prod
        (anisotropicObservationTerminalSpinKernel D μ
          (Q (nativeStreamingGeneratedEndpointVertex U v).depth)
          (nativeStreamingVertexState (nativeStreamingGeneratedEndpointVertex U v) z.1 z.2.2)) =
      (anisotropicObservationTerminalSpinKernel D μ r z.2.1).prod
        (anisotropicObservationTerminalSpinKernel D μ (q v.depth)
          (nativeStreamingVertexState v z.1 (nativeStreamingGeneratedEndpointRecordProject U z.2.2)))
    rw [nativeStreamingGeneratedEndpointVertex_depth]
    simp only [Q,q,nativeStreamingGeneratedEndpointClock_succ,hz]
  have H := compProd_comap_map_history L π hπ
    (printedGeneratedEdgeVertexObservedSpinKernel D μ q U.tree v r)
  rw [printedGeneratedEndpoint_edge_joint_law] at H
  have H' : ((L ⊗ₘ printedGeneratedEdgeVertexObservedSpinKernel D μ Q V.tree
      (nativeStreamingGeneratedEndpointVertex U v) r).map (Prod.map π id)) =
    ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q U.tree e r) ⊗ₘ
      printedGeneratedEdgeVertexObservedSpinKernel D μ q U.tree v r) := by
    rw [Measure.compProd_congr hk]
    exact H
  let dropV := fun z : (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) V.tree)) ×
        (Configuration n × Configuration n) => ((z.1.1,z.1.2.2),z.2)
  let dropU := fun z : (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) U.tree)) ×
        (Configuration n × Configuration n) => ((z.1.1,z.1.2.2),z.2)
  have hdV : Measurable dropV :=
    (measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd
  have hdU : Measurable dropU :=
    (measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd
  rw [←printedGeneratedEdgeVertexObservedLaw_eq_probability D μ a Q hQ hQ0 V.tree _ _ r hcell,
    ←printedGeneratedEdgeVertexObservedLaw_eq_probability D μ a q
      (nativeStreamingGeneratedComponentClock_antitone U h)
      (nativeStreamingGeneratedComponentClock_terminal U h) U.tree e v r hr]
  change ((L ⊗ₘ printedGeneratedEdgeVertexObservedSpinKernel D μ Q V.tree
    (nativeStreamingGeneratedEndpointVertex U v) r).map dropV).map
      (printedGeneratedEndpointCrossRecordProject U) =
    ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q U.tree e r) ⊗ₘ
      printedGeneratedEdgeVertexObservedSpinKernel D μ q U.tree v r).map dropU
  rw [Measure.map_map (measurable_printedGeneratedEndpointCrossRecordProject U) hdV,
    show printedGeneratedEndpointCrossRecordProject U ∘ dropV = dropU ∘ Prod.map π id from rfl,
    ←Measure.map_map hdU (hπ.prodMap measurable_id),H']

end QuantitativeFollowup
