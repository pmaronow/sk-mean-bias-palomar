module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverLeafGeometry
public import QuantitativeFollowup.SupportingGeneratedEndpointOldPairs

@[expose] public section

/-! Every old leaf pair keeps its physical common clock in each actual
two-origin successor chart. Both draws still refer to the original tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def printedGeneratedMixedCrossOldLeaf
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0<v.depth) (hvJ : v.depth<U.depth)
    (i : ObservationLeaf U.tree) :
    ObservationLeaf (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ).tree :=
  finiteCascadeLinearCrossOldLeaf (nativeStreamingGeneratedEdgeVertex U e)
    (nativeStreamingGeneratedMixedRefinedVertex U e v)
    (observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision e.depth) U.tree i)

def printedGeneratedCrossEdgeOldLeaf
    (U : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) (i : ObservationLeaf U.tree) :
    ObservationLeaf (nativeStreamingGeneratedCrossEdgeComponent U e f k).tree :=
  finiteCascadeLinearCrossOldLeaf (nativeStreamingGeneratedCrossEdgeFirstVertex U e f k)
    (nativeStreamingGeneratedCrossEdgeSecondVertex U e f k)
    (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree i)

def printedGeneratedOriginCrossChartOldLeaf
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart) (i : ObservationLeaf U.tree) :
    ObservationLeaf (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree :=
  match γ₁,γ₂ with
  | .inl v,.inl w => finiteCascadeLinearCrossOldLeaf
      (printedGeneratedOriginChartFork U v) (printedGeneratedOriginChartFork U w) i
  | .inr (.inl e),.inl v => printedGeneratedMixedCrossOldLeaf U
      (printedGeneratedOriginChartEdge U e) (printedGeneratedOriginChartFork U v)
      (printedGeneratedOriginChartFork_interior U v).1 (printedGeneratedOriginChartFork_interior U v).2 i
  | .inl v,.inr (.inl e) => printedGeneratedMixedCrossOldLeaf U
      (printedGeneratedOriginChartEdge U e) (printedGeneratedOriginChartFork U v)
      (printedGeneratedOriginChartFork_interior U v).1 (printedGeneratedOriginChartFork_interior U v).2 i
  | .inr (.inl e),.inr (.inl f) => printedGeneratedCrossEdgeOldLeaf U
      (printedGeneratedOriginChartEdge U e) (printedGeneratedOriginChartEdge U f) k i
  | .inr (.inr _),.inl v => finiteCascadeLinearCrossOldLeaf
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U v))
      (nativeStreamingGeneratedEndpointLeaf U i)
  | .inl v,.inr (.inr _) => finiteCascadeLinearCrossOldLeaf
      (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U v))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointLeaf U i)
  | .inr (.inl e),.inr (.inr _) => printedGeneratedMixedCrossOldLeaf
      (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U e))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
      (nativeStreamingGeneratedEndpointLeaf U i)
  | .inr (.inr _),.inr (.inl e) => printedGeneratedMixedCrossOldLeaf
      (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U e))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
      (nativeStreamingGeneratedEndpointLeaf U i)
  | .inr (.inr _),.inr (.inr _) => finiteCascadeLinearCrossOldLeaf
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointLeaf U i)

private theorem vertexOldClock
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<U.depth) (hw0 : 0<w.depth) (hwJ : w.depth<U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) (i j : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedCrossVertexComponent U v w hv0 hvJ hw0 hwJ)
      (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))
        (nativeStreamingGeneratedComponentClock U h w.depth))
      (observationCommonLevel _ (finiteCascadeLinearCrossOldLeaf v w i)
        (finiteCascadeLinearCrossOldLeaf v w j)) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j) := by
  rw [←printedGeneratedCrossVertexAppend_physical U v w h hh,
    nativeStreamingGeneratedCrossVertexComponent_clock_append,
    finiteCascadeLinearCrossOldLeaf_commonLevel]

private theorem mixedOldClock
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0<v.depth) (hvJ : v.depth<U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock U h e.depth) (i j : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ)
      (Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth))
      (observationCommonLevel _ (printedGeneratedMixedCrossOldLeaf U e v hv0 hvJ i)
        (printedGeneratedMixedCrossOldLeaf U e v hv0 hvJ j)) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j) := by
  rw [printedGeneratedMixedCrossClock_physical U e v hv0 hvJ h r hh hr]
  change nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h) e.depth r
    (observationCommonLevel _
      (finiteCascadeLinearCrossOldLeaf (nativeStreamingGeneratedEdgeVertex U e)
        (nativeStreamingGeneratedMixedRefinedVertex U e v)
        (observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision e.depth) U.tree i))
      (finiteCascadeLinearCrossOldLeaf (nativeStreamingGeneratedEdgeVertex U e)
        (nativeStreamingGeneratedMixedRefinedVertex U e v)
        (observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision e.depth) U.tree j))) = _
  rw [finiteCascadeLinearCrossOldLeaf_commonLevel]
  change nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h) e.depth r
    (observationCommonLevel (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) U.tree)
      (observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision e.depth) U.tree i)
      (observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision e.depth) U.tree j)) = _
  rw [observationRefinementLeafEmbed_commonLevel, nativeStreamingEdgeSchedule_refinement]

private theorem edgeOldClock
    (U : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock U h e.depth)
    (hl : nativeStreamingGeneratedComponentClock U h (f.depth+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock U h f.depth)
    (hk : k.Holds e.depth f.depth r l) (i j : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedCrossEdgeComponent U e f k)
      (Fin.snoc (Fin.snoc h r) l)
      (observationCommonLevel _ (printedGeneratedCrossEdgeOldLeaf U e f k i)
        (printedGeneratedCrossEdgeOldLeaf U e f k j)) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j) := by
  rw [nativeStreamingGeneratedCrossEdgeComponent_clock]
  change nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedCrossEdgeObservedComponent U e f k)
    (nativeStreamingGeneratedCrossEdgeAppend h r l)
    (observationCommonLevel _ (printedGeneratedCrossEdgeOldLeaf U e f k i)
      (printedGeneratedCrossEdgeOldLeaf U e f k j)) = _
  rw [nativeStreamingGeneratedCrossEdgeObservedComponent_clock_append U e f k h r l hh hr hl hk]
  change nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock U h) e.depth f.depth r l
    (observationCommonLevel _
      (finiteCascadeLinearCrossOldLeaf (nativeStreamingGeneratedCrossEdgeFirstVertex U e f k)
        (nativeStreamingGeneratedCrossEdgeSecondVertex U e f k)
        (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree i))
      (finiteCascadeLinearCrossOldLeaf (nativeStreamingGeneratedCrossEdgeFirstVertex U e f k)
        (nativeStreamingGeneratedCrossEdgeSecondVertex U e f k)
        (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree j))) = _
  rw [finiteCascadeLinearCrossOldLeaf_commonLevel]
  change nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock U h) e.depth f.depth r l
    (observationCommonLevel (observationRefineTree nativeStreamingPairObservationSubdivision U.tree)
      (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree i)
      (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree j)) = _
  rw [observationRefinementLeafEmbed_commonLevel, nativeStreamingPairObservationSchedule_refinement]

private theorem endpointVertexOldClock
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) (i j : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (printedGeneratedEndpointCrossVertexComponent U v w)
      (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))
        (nativeStreamingGeneratedComponentClock U h w.depth))
      (observationCommonLevel _
        (finiteCascadeLinearCrossOldLeaf (nativeStreamingGeneratedEndpointVertex U v)
          (nativeStreamingGeneratedEndpointVertex U w) (nativeStreamingGeneratedEndpointLeaf U i))
        (finiteCascadeLinearCrossOldLeaf (nativeStreamingGeneratedEndpointVertex U v)
          (nativeStreamingGeneratedEndpointVertex U w) (nativeStreamingGeneratedEndpointLeaf U j))) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j) := by
  have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
    rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
  have H := vertexOldClock (nativeStreamingGeneratedEndpointComponent U)
    (nativeStreamingGeneratedEndpointVertex U v) (nativeStreamingGeneratedEndpointVertex U w)
    (nativeStreamingGeneratedEndpointVertex_interior U v).1 (nativeStreamingGeneratedEndpointVertex_interior U v).2
    (nativeStreamingGeneratedEndpointVertex_interior U w).1 (nativeStreamingGeneratedEndpointVertex_interior U w).2
    h hp (nativeStreamingGeneratedEndpointLeaf U i) (nativeStreamingGeneratedEndpointLeaf U j)
  rw [nativeStreamingGeneratedEndpointVertex_clock U h v,
    nativeStreamingGeneratedEndpointVertex_clock U h w] at H
  exact H.trans (nativeStreamingGeneratedEndpointOldLeaves_commonClock U h i j)

private theorem endpointMixedOldClock
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock U h e.depth)
    (i j : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (printedGeneratedEndpointMixedCrossComponent U e v)
      (Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth))
      (observationCommonLevel _
        (printedGeneratedMixedCrossOldLeaf (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U e) (nativeStreamingGeneratedEndpointVertex U v)
          (nativeStreamingGeneratedEndpointVertex_interior U v).1 (nativeStreamingGeneratedEndpointVertex_interior U v).2
          (nativeStreamingGeneratedEndpointLeaf U i))
        (printedGeneratedMixedCrossOldLeaf (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U e) (nativeStreamingGeneratedEndpointVertex U v)
          (nativeStreamingGeneratedEndpointVertex_interior U v).1 (nativeStreamingGeneratedEndpointVertex_interior U v).2
          (nativeStreamingGeneratedEndpointLeaf U j))) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j) := by
  have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
    rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
  have H := mixedOldClock (nativeStreamingGeneratedEndpointComponent U)
    (printedGeneratedEndpointEdge U e) (nativeStreamingGeneratedEndpointVertex U v)
    (nativeStreamingGeneratedEndpointVertex_interior U v).1 (nativeStreamingGeneratedEndpointVertex_interior U v).2
    h r hp (printedGeneratedEndpointEdge_cell U e h r hr)
    (nativeStreamingGeneratedEndpointLeaf U i) (nativeStreamingGeneratedEndpointLeaf U j)
  rw [nativeStreamingGeneratedEndpointVertex_clock U h v] at H
  exact H.trans (nativeStreamingGeneratedEndpointOldLeaves_commonClock U h i j)

theorem printedGeneratedOriginCrossChart_old_pair_clock
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r) (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l)
    (i j : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
      (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l)
      (observationCommonLevel _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k i)
        (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k j)) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j) := by
  rcases γ₁ with v | (v | u) <;> rcases γ₂ with w | (w | t)
  · exact vertexOldClock U _ _
      (printedGeneratedOriginChartFork_interior U v).1 (printedGeneratedOriginChartFork_interior U v).2
      (printedGeneratedOriginChartFork_interior U w).1 (printedGeneratedOriginChartFork_interior U w).2 h hh i j
  · let e := printedGeneratedOriginChartEdge U w
    let z := printedGeneratedOriginChartFork U v
    have hz := printedGeneratedOriginChartFork_interior U v
    change nativeStreamingGeneratedComponentClock (printedGeneratedCrossSwapComponent
        (nativeStreamingGeneratedMixedCrossComponent U e z hz.1 hz.2))
      (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h z.depth)) l)
      (observationCommonLevel _ (printedGeneratedMixedCrossOldLeaf U e z hz.1 hz.2 i)
        (printedGeneratedMixedCrossOldLeaf U e z hz.1 hz.2 j)) = _
    rw [printedGeneratedCrossSwapClock_append]
    exact mixedOldClock U e z hz.1 hz.2 h l hh hl i j
  · exact endpointVertexOldClock U (printedGeneratedOriginChartFork U v) (.root U.tree) h hh i j
  · exact mixedOldClock U _ _
      (printedGeneratedOriginChartFork_interior U w).1 (printedGeneratedOriginChartFork_interior U w).2 h r hh hr i j
  · exact edgeOldClock U _ _ k h r l hh hr hl hk i j
  · exact endpointMixedOldClock U (printedGeneratedOriginChartEdge U v) (.root U.tree) h r hh hr i j
  · exact endpointVertexOldClock U (.root U.tree) (printedGeneratedOriginChartFork U w) h hh i j
  · let P := nativeStreamingGeneratedEndpointComponent U
    let e := printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U w)
    let z := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
    have hz := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
    change nativeStreamingGeneratedComponentClock (printedGeneratedCrossSwapComponent
        (nativeStreamingGeneratedMixedCrossComponent P e z hz.1 hz.2))
      (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h U.depth)) l)
      (observationCommonLevel _
        (printedGeneratedMixedCrossOldLeaf P e z hz.1 hz.2 (nativeStreamingGeneratedEndpointLeaf U i))
        (printedGeneratedMixedCrossOldLeaf P e z hz.1 hz.2 (nativeStreamingGeneratedEndpointLeaf U j))) = _
    rw [printedGeneratedCrossSwapClock_append]
    exact endpointMixedOldClock U (printedGeneratedOriginChartEdge U w) (.root U.tree) h l hh hl i j
  · exact endpointVertexOldClock U (.root U.tree) (.root U.tree) h hh i j

end QuantitativeFollowup
