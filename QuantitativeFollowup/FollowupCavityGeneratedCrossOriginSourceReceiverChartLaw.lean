module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossEdgePatternsLaw

@[expose] public section

/-! The nine concrete original-origin chart combinations receive the
actual native cross law, retaining the complete original record and both
ordered fresh spins. Both choices refer to the original component. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

private theorem crossChart_endpoint_vertex_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (printedGeneratedEndpointCrossVertexComponent U v w)
        (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))
          (nativeStreamingGeneratedComponentClock U h w.depth)))
      (printedGeneratedEndpointCrossVertexComponent U v w).tree).map
      (printedGeneratedEndpointCrossRecordProject U ∘
        printedGeneratedCrossVertexRecordProjection (nativeStreamingGeneratedEndpointComponent U)
          (nativeStreamingGeneratedEndpointVertex U v) (nativeStreamingGeneratedEndpointVertex U w)
          (nativeStreamingGeneratedEndpointVertex_interior U v).1
          (nativeStreamingGeneratedEndpointVertex_interior U v).2
          (nativeStreamingGeneratedEndpointVertex_interior U w).1
          (nativeStreamingGeneratedEndpointVertex_interior U w).2) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (.vertex v) (.vertex w) : Measure _) := by
  have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
    rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
  have H := printedGeneratedCrossVertex_full_record_law_physical D μ a
    (nativeStreamingGeneratedEndpointComponent U)
    (nativeStreamingGeneratedEndpointVertex U v) (nativeStreamingGeneratedEndpointVertex U w)
    (nativeStreamingGeneratedEndpointVertex_interior U v).1
    (nativeStreamingGeneratedEndpointVertex_interior U v).2
    (nativeStreamingGeneratedEndpointVertex_interior U w).1
    (nativeStreamingGeneratedEndpointVertex_interior U w).2 h hp
  rw [nativeStreamingGeneratedEndpointVertex_clock,nativeStreamingGeneratedEndpointVertex_clock] at H
  have H' := congrArg (fun P : Measure (CavityGeneratedCrossOriginalRecordPair
    (AnisotropicObservationState n) (Configuration n) (nativeStreamingGeneratedEndpointComponent U)) =>
      P.map (printedGeneratedEndpointCrossRecordProject U)) H
  rw [Measure.map_map (measurable_printedGeneratedEndpointCrossRecordProject U)
    (measurable_printedGeneratedCrossVertexRecordProjection _ _ _ _ _ _ _),
    nativeStreamingOriginCrossProbability_vertex_vertex D μ a _
      (nativeStreamingGeneratedComponentClock_antitone (nativeStreamingGeneratedEndpointComponent U) h)
      (nativeStreamingGeneratedComponentClock_terminal (nativeStreamingGeneratedEndpointComponent U) h)] at H'
  simp only [nativeStreamingGeneratedEndpointComponent_clock] at H'
  rw [printedGeneratedEndpointCrossVertexLaw_project] at H'
  rw [nativeStreamingOriginCrossProbability_vertex_vertex D μ a _
    (nativeStreamingGeneratedComponentClock_antitone U h) (nativeStreamingGeneratedComponentClock_terminal U h)]
  exact H'

private theorem crossChart_endpoint_mixed_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (printedGeneratedEndpointMixedCrossComponent U e v)
        (Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth)))
      (printedGeneratedEndpointMixedCrossComponent U e v).tree).map
      (printedGeneratedEndpointCrossRecordProject U ∘
        nativeStreamingGeneratedMixedCrossRecordProjection (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U e) (nativeStreamingGeneratedEndpointVertex U v)
          (nativeStreamingGeneratedEndpointVertex_interior U v).1
          (nativeStreamingGeneratedEndpointVertex_interior U v).2) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (.edge e r) (.vertex v) : Measure _) := by
  have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
    rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
  have H := printedGeneratedMixedCross_full_record_law_physical D μ a
    (nativeStreamingGeneratedEndpointComponent U) (printedGeneratedEndpointEdge U e)
    (nativeStreamingGeneratedEndpointVertex U v)
    (nativeStreamingGeneratedEndpointVertex_interior U v).1
    (nativeStreamingGeneratedEndpointVertex_interior U v).2 h r hp
    (printedGeneratedEndpointEdge_cell U e h r hr)
  rw [nativeStreamingGeneratedEndpointVertex_clock] at H
  have H' := congrArg (fun P : Measure (CavityGeneratedCrossOriginalRecordPair
    (AnisotropicObservationState n) (Configuration n) (nativeStreamingGeneratedEndpointComponent U)) =>
      P.map (printedGeneratedEndpointCrossRecordProject U)) H
  rw [Measure.map_map (measurable_printedGeneratedEndpointCrossRecordProject U)
    (measurable_nativeStreamingGeneratedMixedCrossRecordProjection _ _ _ _ _)] at H'
  simp only [nativeStreamingGeneratedEndpointComponent_clock] at H'
  rw [printedGeneratedEndpointEdgeVertexProbability_project D μ a U h e v r hr] at H'
  exact H'

theorem printedGeneratedOriginCrossChart_full_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r)
    (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l))
      (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree).map
      (printedGeneratedOriginCrossChartRecordProjection U γ₁ γ₂ k) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (printedGeneratedOriginCrossChartOrigin U γ₁ r)
          (printedGeneratedOriginCrossChartOrigin U γ₂ l) : Measure _) := by
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  · exact printedGeneratedCrossVertex_full_record_law_physical D μ a U
      (printedGeneratedOriginChartFork U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2 h hh
  · change (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (printedGeneratedCrossSwapComponent
        (nativeStreamingGeneratedMixedCrossComponent U (printedGeneratedOriginChartEdge U j)
          (printedGeneratedOriginChartFork U i)
          (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2))
        (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h
          (printedGeneratedOriginChartFork U i).depth)) l))
      (nativeStreamingGeneratedMixedCrossComponent U (printedGeneratedOriginChartEdge U j)
        (printedGeneratedOriginChartFork U i)
        (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2).tree).map
      ((Prod.map id Prod.swap) ∘ nativeStreamingGeneratedMixedCrossRecordProjection U
        (printedGeneratedOriginChartEdge U j) (printedGeneratedOriginChartFork U i)
        (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h) U.tree
        (.edge (printedGeneratedOriginChartEdge U j) l) (.vertex (printedGeneratedOriginChartFork U i)) :
          Measure (CavityGeneratedCrossOriginalRecordPair (AnisotropicObservationState n) (Configuration n) U)).map
        (Prod.map id Prod.swap)
    rw [printedGeneratedCrossSwapClock_append,
      ←Measure.map_map (measurable_id.prodMap measurable_swap)
        (measurable_nativeStreamingGeneratedMixedCrossRecordProjection _ _ _ _ _),
      printedGeneratedMixedCross_full_record_law_physical D μ a U _ _ _ _ h l hh hl]
  · exact crossChart_endpoint_vertex_law D μ a U (printedGeneratedOriginChartFork U i) (.root U.tree) h hh
  · exact printedGeneratedMixedCross_full_record_law_physical D μ a U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2 h r hh hr
  · exact nativeStreamingGeneratedCrossEdge_full_record_law D μ a U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartEdge U j) k h r l hh hr hl hk
  · exact crossChart_endpoint_mixed_law D μ a U (printedGeneratedOriginChartEdge U i) (.root U.tree) h r hh hr
  · exact crossChart_endpoint_vertex_law D μ a U (.root U.tree) (printedGeneratedOriginChartFork U j) h hh
  · change (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (printedGeneratedCrossSwapComponent
        (printedGeneratedEndpointMixedCrossComponent U (printedGeneratedOriginChartEdge U j) (.root U.tree)))
        (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h U.depth)) l))
      (printedGeneratedEndpointMixedCrossComponent U (printedGeneratedOriginChartEdge U j) (.root U.tree)).tree).map
      ((Prod.map id Prod.swap) ∘ printedGeneratedEndpointCrossRecordProject U ∘
        nativeStreamingGeneratedMixedCrossRecordProjection (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U j))
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h) U.tree
        (.edge (printedGeneratedOriginChartEdge U j) l) (.vertex (.root U.tree)) :
          Measure (CavityGeneratedCrossOriginalRecordPair (AnisotropicObservationState n) (Configuration n) U)).map
        (Prod.map id Prod.swap)
    rw [printedGeneratedCrossSwapClock_append,
      ←Measure.map_map (measurable_id.prodMap measurable_swap)
        ((measurable_printedGeneratedEndpointCrossRecordProject U).comp
          (measurable_nativeStreamingGeneratedMixedCrossRecordProjection _ _ _ _ _)),
      crossChart_endpoint_mixed_law D μ a U _ (.root U.tree) h l hh hl]
  · exact crossChart_endpoint_vertex_law D μ a U (.root U.tree) (.root U.tree) h hh

end QuantitativeFollowup
