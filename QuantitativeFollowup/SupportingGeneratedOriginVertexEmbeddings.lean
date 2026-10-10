module
public import QuantitativeFollowup.SupportingGeneratedOriginComponentCharts
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexRefinement
public import FourPapersCommon.FiniteCascadeContinuationVertexGeometry

@[expose] public section

/-! Every original vertex has a specified image in each one-origin component.
The edge image is refined before grafting, and the root image is padded before
grafting.  The depth changes are those of the actual genealogy, while the
physical clock of the original vertex is retained. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def printedGeneratedOriginChartOldDepth (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (j : ℕ) : ℕ := match γ with
  | .inl _ => j
  | .inr (.inl i) => observationRefinementDepth
      (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U i).depth) j
  | .inr (.inr _) => j+1

@[reducible] def printedGeneratedOriginChartVertexEmbed
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (v : FiniteCascadeRecordVertex U.tree) :
    FiniteCascadeRecordVertex (printedGeneratedOriginChartComponent U γ k).tree := match γ with
  | .inl i => finiteCascadeContinuationVertexEmbed k.continuation
      (printedGeneratedOriginChartFork U i) v
  | .inr (.inl i) => finiteCascadeContinuationVertexEmbed k.continuation
      (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i))
      (nativeStreamingRefinementVertexEmbed
        (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U i).depth) U.tree v)
  | .inr (.inr _) => finiteCascadeContinuationVertexEmbed k.continuation
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U v)

theorem printedGeneratedOriginChartVertexEmbed_depth
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (v : FiniteCascadeRecordVertex U.tree) :
    (printedGeneratedOriginChartVertexEmbed U γ k v).depth =
      printedGeneratedOriginChartOldDepth U γ v.depth := by
  rcases γ with i | (i | u)
  · exact finiteCascadeContinuationVertexEmbed_depth k.continuation _ v
  · change (finiteCascadeContinuationVertexEmbed k.continuation _
        (nativeStreamingRefinementVertexEmbed _ U.tree v)).depth = _
    rw [finiteCascadeContinuationVertexEmbed_depth, nativeStreamingRefinementVertexEmbed_depth]
    rfl
  · change (finiteCascadeContinuationVertexEmbed k.continuation _
        (nativeStreamingGeneratedEndpointVertex U v)).depth = _
    rw [finiteCascadeContinuationVertexEmbed_depth, nativeStreamingGeneratedEndpointVertex_depth]
    rfl

theorem printedGeneratedOriginChartVertexEmbed_raw_clock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (v : FiniteCascadeRecordVertex U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    (cavityGeneratedFiniteClockLabels (printedGeneratedOriginChartComponent U γ k).label
      (printedGeneratedOriginChartVertexEmbed U γ k v).depth).value
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r)) =
      nativeStreamingGeneratedComponentClock U h v.depth := by
  rcases γ with i | (i | u)
  · rw [printedGeneratedOriginChartVertexEmbed_depth]
    exact printedGeneratedVertexComponent_snoc_raw U (printedGeneratedOriginChartFork U i)
      (printedGeneratedOriginChartFork_interior U i).1
      (printedGeneratedOriginChartFork_interior U i).2 k h hh v.depth
  · rw [printedGeneratedOriginChartVertexEmbed_depth]
    change (cavityGeneratedFiniteClockLabels
      (nativeStreamingGeneratedEdgeLabels U (printedGeneratedOriginChartEdge U i))
      (observationRefinementDepth
        (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U i).depth) v.depth)).value
          (Fin.snoc h r) = _
    rw [nativeStreamingGeneratedEdgeLabels_global,
      nativeStreamingGeneratedEdgeGlobalLabels_refinement,
      CavityGeneratedClockLabel.append_reindex_value, cavityGeneratedHistoryPrefix_snoc]
    exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh v.depth
  · have hhp : h ∈ nativeStreamingGeneratedComponentOrderSet
        (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have he := printedGeneratedVertexComponent_snoc_raw
      (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 k h hhp
      (nativeStreamingGeneratedEndpointVertex U v).depth
    rw [nativeStreamingGeneratedEndpointVertex_clock,
      nativeStreamingGeneratedEndpointVertex_clock] at he
    change (cavityGeneratedFiniteClockLabels
      (nativeStreamingGeneratedVertexComponent (nativeStreamingGeneratedEndpointComponent U)
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 k).label
      (finiteCascadeContinuationVertexEmbed k.continuation _
        (nativeStreamingGeneratedEndpointVertex U v)).depth).value
          (Fin.snoc h (nativeStreamingGeneratedComponentClock U h U.depth)) = _
    rw [finiteCascadeContinuationVertexEmbed_depth]
    exact he

theorem printedGeneratedOriginChartVertexEmbed_clock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (v : FiniteCascadeRecordVertex U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ k)
      (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
      (printedGeneratedOriginChartVertexEmbed U γ k v).depth =
        nativeStreamingGeneratedComponentClock U h v.depth := by
  have ho := printedGeneratedOriginChartComponent_snoc_order U γ k h r hh hr
  rw [←nativeStreamingGeneratedComponent_raw_eq_clock_of_order _ _ ho]
  exact printedGeneratedOriginChartVertexEmbed_raw_clock U γ k v h r hh

theorem printedGeneratedOriginChartVertexEmbed_raw_original
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (v : FiniteCascadeRecordVertex U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    (cavityGeneratedFiniteClockLabels (printedGeneratedOriginChartComponent U γ k).label
      (printedGeneratedOriginChartVertexEmbed U γ k v).depth).value
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r)) =
      (cavityGeneratedFiniteClockLabels U.label v.depth).value h := by
  rw [nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh v.depth]
  exact printedGeneratedOriginChartVertexEmbed_raw_clock U γ k v h r hh

end QuantitativeFollowup
