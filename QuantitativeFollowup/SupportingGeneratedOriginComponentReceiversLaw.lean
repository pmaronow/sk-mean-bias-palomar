module
public import QuantitativeFollowup.SupportingGeneratedOriginComponentReceiversDefinitions

@[expose] public section

/-! The actual chart output law projects to the original single/current
origin law. Endpoint padding is removed using its true identity transition,
and the edge case retains the complete original record through refinement. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem printedGeneratedEndpointOriginProbability_projection
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex U.tree) (k : NativeStreamingGeneratedVertexKind) :
    (printedGeneratedOriginKindProbability D μ a (nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedEndpointComponent U) h)
      (nativeStreamingGeneratedEndpointComponent U).tree
      (.vertex (nativeStreamingGeneratedEndpointVertex U v)) k :
        Measure (PrintedGeneratedComponentRecord n (nativeStreamingGeneratedEndpointComponent U) ×
          k.Mark (Configuration (n+1)))).map
      (Prod.map (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U)) id) =
    (printedGeneratedOriginKindProbability D μ a (nativeStreamingGeneratedComponentClock U h)
      U.tree (.vertex v) k : Measure (PrintedGeneratedComponentRecord n U ×
        k.Mark (Configuration (n+1)))) := by
  rw [nativeStreamingGeneratedEndpointComponent_clock]
  have hQ : Antitone (nativeStreamingGeneratedEndpointClock U h) := by
    rw [←nativeStreamingGeneratedEndpointComponent_clock]
    exact nativeStreamingGeneratedComponentClock_antitone _ h
  have hQ0 := nativeStreamingGeneratedEndpointClock_zero U h
  have hq := nativeStreamingGeneratedComponentClock_antitone U h
  have hq0 := nativeStreamingGeneratedComponentClock_terminal U h
  cases k with
  | single =>
      change (nativeStreamingSingleVertexProbability D μ a (nativeStreamingGeneratedEndpointClock U h)
        (nativeStreamingGeneratedEndpointComponent U).tree (nativeStreamingGeneratedEndpointVertex U v) :
          Measure (PrintedGeneratedComponentRecord n (nativeStreamingGeneratedEndpointComponent U) ×
            Configuration (n+1))).map _ =
        (nativeStreamingSingleVertexProbability D μ a (nativeStreamingGeneratedComponentClock U h)
          U.tree v : Measure (PrintedGeneratedComponentRecord n U × Configuration (n+1)))
      rw [nativeStreamingSingleVertexProbability_eq_law D μ a _ hQ hQ0,
        nativeStreamingSingleVertexProbability_eq_law D μ a _ hq hq0]
      exact nativeStreamingGeneratedEndpoint_single_law D μ a U h v
  | current =>
      change (nativeStreamingCurrentPairProbability D μ a (nativeStreamingGeneratedEndpointClock U h)
        (nativeStreamingGeneratedEndpointComponent U).tree (nativeStreamingGeneratedEndpointVertex U v) :
          Measure (PrintedGeneratedComponentRecord n (nativeStreamingGeneratedEndpointComponent U) ×
            (Configuration (n+1) × Configuration (n+1)))).map _ =
        (nativeStreamingCurrentPairProbability D μ a (nativeStreamingGeneratedComponentClock U h)
          U.tree v : Measure (PrintedGeneratedComponentRecord n U ×
            (Configuration (n+1) × Configuration (n+1))))
      rw [nativeStreamingCurrentPairProbability_eq_law D μ a _ hQ hQ0,
        nativeStreamingCurrentPairProbability_eq_law D μ a _ hq hq0]
      exact nativeStreamingGeneratedEndpoint_current_law D μ a U h v

theorem printedGeneratedEdgeOriginProbability_projection
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth)
    (k : NativeStreamingGeneratedVertexKind) :
    (printedGeneratedOriginKindProbability D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeComponent U e k)
        (Fin.snoc h r)) (nativeStreamingGeneratedEdgeObservedComponent U e).tree
      (.vertex (nativeStreamingGeneratedEdgeVertex U e)) k :
        Measure (PrintedGeneratedComponentRecord n (nativeStreamingGeneratedEdgeObservedComponent U e) ×
          k.Mark (Configuration (n+1)))).map
      (Prod.map (Prod.map id (observationRefinementProject
        (nativeStreamingEdgeSubdivision e.depth) U.tree)) id) =
    (printedGeneratedOriginKindProbability D μ a (nativeStreamingGeneratedComponentClock U h)
      U.tree (.edge e r) k : Measure (PrintedGeneratedComponentRecord n U ×
        k.Mark (Configuration (n+1)))) := by
  rw [nativeStreamingGeneratedEdgeComponent_clock,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc U e h r hh hr]
  cases k <;> simp only [printedGeneratedOriginKindProbability,
    nativeStreamingOriginSingleProbability, nativeStreamingOriginCurrentProbability,
    nativeStreamingEdgeSingleMarkProbability, nativeStreamingEdgeCurrentPairProbability,
    ProbabilityMeasure.toMeasure_map, Prod.map_def, id_eq,
    nativeStreamingGeneratedEdgeVertex, nativeStreamingGeneratedEdgeObservedComponent]

theorem printedGeneratedOriginChartRecordProject_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) :
    (printedGeneratedComponentLaw D μ a (printedGeneratedOriginChartComponent U γ k)
      (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))).map
        (printedGeneratedOriginChartRecordProject U γ k) =
    (printedGeneratedOriginKindProbability D μ a (nativeStreamingGeneratedComponentClock U h)
      U.tree (printedGeneratedOriginChartOrigin U γ r) k :
        Measure (PrintedGeneratedComponentRecord n U × k.Mark (Configuration (n+1)))) := by
  rcases γ with i | (i | u)
  · change (anisotropicRecordedProfileTreeLaw D μ a
      (printedGeneratedComponentClock
        (nativeStreamingGeneratedVertexComponent U (printedGeneratedOriginChartFork U i)
          (printedGeneratedOriginChartFork_interior U i).1
          (printedGeneratedOriginChartFork_interior U i).2 k)
        (Fin.snoc h (nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartFork U i).depth)))
      (finiteCascadeContinuationGraft k.continuation (printedGeneratedOriginChartFork U i))).map
        (printedGeneratedVertexMarkedRecordProject k (printedGeneratedOriginChartFork U i)) = _
    rw [printedGeneratedComponentClock_eq_native,
      printedGeneratedVertexComponent_snoc_clock U _ _ _ k h hh]
    exact printedGeneratedVertexMarkedRecordProject_law D μ a _ _ _ k
  · let e := printedGeneratedOriginChartEdge U i
    let post := Prod.map
      (Prod.map (id : AnisotropicObservationState (n+1) → AnisotropicObservationState (n+1))
        (observationRefinementProject (E:=AnisotropicObservationState (n+1))
          (S:=Configuration (n+1)) (nativeStreamingEdgeSubdivision e.depth) U.tree))
      (id : k.Mark (Configuration (n+1)) → k.Mark (Configuration (n+1)))
    have hpost : Measurable post :=
      (measurable_id.prodMap (measurable_observationRefinementProject _ U.tree)).prodMap measurable_id
    have hbase := measurable_printedGeneratedVertexMarkedRecordProject (n:=n) k
      (nativeStreamingGeneratedEdgeVertex U e)
    change (anisotropicRecordedProfileTreeLaw D μ a
      (printedGeneratedComponentClock (nativeStreamingGeneratedEdgeComponent U e k) (Fin.snoc h r))
      (finiteCascadeContinuationGraft k.continuation (nativeStreamingGeneratedEdgeVertex U e))).map
        (post ∘ printedGeneratedVertexMarkedRecordProject k (nativeStreamingGeneratedEdgeVertex U e)) = _
    rw [printedGeneratedComponentClock_eq_native,←Measure.map_map hpost hbase,
      printedGeneratedVertexMarkedRecordProject_law]
    exact printedGeneratedEdgeOriginProbability_projection D μ a U e h r hh hr k
  · let V := nativeStreamingGeneratedEndpointComponent U
    let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
    let post := Prod.map
      (Prod.map (id : AnisotropicObservationState (n+1) → AnisotropicObservationState (n+1))
        (nativeStreamingGeneratedEndpointRecordProject (E:=AnisotropicObservationState (n+1))
          (S:=Configuration (n+1)) U))
      (id : k.Mark (Configuration (n+1)) → k.Mark (Configuration (n+1)))
    have hpost : Measurable post :=
      (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject U)).prodMap measurable_id
    have hbase := measurable_printedGeneratedVertexMarkedRecordProject (n:=n) k v
    have hhv : h ∈ nativeStreamingGeneratedComponentOrderSet V := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have hc : nativeStreamingGeneratedComponentClock V h v.depth =
        nativeStreamingGeneratedComponentClock U h U.depth := by
      exact nativeStreamingGeneratedEndpointVertex_clock U h (.root U.tree)
    change (anisotropicRecordedProfileTreeLaw D μ a
      (printedGeneratedComponentClock
        (nativeStreamingGeneratedVertexComponent V v
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 k)
        (Fin.snoc h (nativeStreamingGeneratedComponentClock U h U.depth)))
      (finiteCascadeContinuationGraft k.continuation v)).map
        (post ∘ printedGeneratedVertexMarkedRecordProject k v) = _
    rw [printedGeneratedComponentClock_eq_native,←hc,
      printedGeneratedVertexComponent_snoc_clock V v _ _ k h hhv,
      ←Measure.map_map hpost hbase,printedGeneratedVertexMarkedRecordProject_law]
    exact printedGeneratedEndpointOriginProbability_projection D μ a U h (.root U.tree) k

theorem printedGeneratedOriginChartRecordProject_measurePreserving
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) :
    MeasurePreserving (printedGeneratedOriginChartRecordProject U γ k)
      (printedGeneratedComponentLaw D μ a (printedGeneratedOriginChartComponent U γ k)
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r)))
      (printedGeneratedOriginKindProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (printedGeneratedOriginChartOrigin U γ r) k) :=
  ⟨measurable_printedGeneratedOriginChartRecordProject U γ k,
    printedGeneratedOriginChartRecordProject_law D μ a U γ k h r hh hr⟩

end QuantitativeFollowup
