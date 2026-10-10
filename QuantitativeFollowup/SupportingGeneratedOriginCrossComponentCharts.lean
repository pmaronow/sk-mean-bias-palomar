module
public import QuantitativeFollowup.SupportingGeneratedOriginCrossComponentChartsGeometry

@[expose] public section

/-! Both indices in the cross factory refer to the original component.
Endpoint padding is used exactly for root choices; coordinate relabeling
keeps the two appended coordinates in the original choice order. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

theorem printedGeneratedCrossVertex_order
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (hw0 : 0 < w.depth) (hwJ : w.depth < U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))
      (nativeStreamingGeneratedComponentClock U h w.depth) ∈
        nativeStreamingGeneratedComponentOrderSet
          (nativeStreamingGeneratedCrossVertexComponent U v w hv0 hvJ hw0 hwJ) := by
  let A := nativeStreamingGeneratedVertexComponent U v hv0 hvJ .single
  let z := finiteCascadeContinuationVertexEmbed observationLinearTree v w
  have hz0 : 0 < z.depth := by
    simpa only [z, finiteCascadeContinuationVertexEmbed_depth] using hw0
  have hzJ : z.depth < A.depth := by
    simpa only [A, z, nativeStreamingGeneratedVertexComponent,
      finiteCascadeContinuationVertexEmbed_depth] using hwJ
  have ho := printedGeneratedVertexComponent_snoc_order U v hv0 hvJ .single h hh
  have hc : nativeStreamingGeneratedComponentClock A
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)) z.depth =
        nativeStreamingGeneratedComponentClock U h w.depth := by
    rw [←nativeStreamingGeneratedComponent_raw_eq_clock_of_order A _ ho]
    rw [show z.depth = w.depth from finiteCascadeContinuationVertexEmbed_depth observationLinearTree v w]
    exact printedGeneratedVertexComponent_snoc_raw U v hv0 hvJ .single h hh w.depth
  have H := printedGeneratedVertexComponent_snoc_order A z hz0 hzJ .single
    (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)) ho
  rw [hc] at H
  exact H

theorem printedGeneratedMixedCross_order
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth) :
    Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth) ∈
      nativeStreamingGeneratedComponentOrderSet
        (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ) := by
  let A := nativeStreamingGeneratedEdgeComponent U e .single
  let z := nativeStreamingGeneratedMixedAttachedVertex U e v
  have hz := nativeStreamingGeneratedMixedAttachedVertex_interior U e v hv0 hvJ
  have ho := printedGeneratedEdgeComponent_snoc_order U e .single h r hh hr
  have hc : nativeStreamingGeneratedComponentClock A (Fin.snoc h r) z.depth =
      nativeStreamingGeneratedComponentClock U h v.depth := by
    rw [←nativeStreamingGeneratedComponent_raw_eq_clock_of_order A _ ho]
    change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels U e)
      (finiteCascadeContinuationVertexEmbed observationLinearTree
        (nativeStreamingGeneratedEdgeVertex U e) (nativeStreamingGeneratedMixedRefinedVertex U e v)).depth).value
        (Fin.snoc h r) = _
    rw [finiteCascadeContinuationVertexEmbed_depth, nativeStreamingGeneratedMixedRefinedVertex_depth,
      nativeStreamingGeneratedEdgeLabels_global, nativeStreamingGeneratedEdgeGlobalLabels_refinement,
      CavityGeneratedClockLabel.append_reindex_value, cavityGeneratedHistoryPrefix_snoc]
    exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh v.depth
  have H := printedGeneratedVertexComponent_snoc_order A z hz.1 hz.2 .single (Fin.snoc h r) ho
  rw [hc] at H
  exact H

theorem printedGeneratedCrossEdge_order
    (U : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge U.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth)
    (hl : nativeStreamingGeneratedComponentClock U h (f.depth+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h f.depth)
    (hc : c.Holds e.depth f.depth r l) :
    Fin.snoc (Fin.snoc h r) l ∈ nativeStreamingGeneratedComponentOrderSet
      (nativeStreamingGeneratedCrossEdgeComponent U e f c) := by
  have hq : (fun j => (cavityGeneratedFiniteClockLabels U.label j).value h) =
      nativeStreamingGeneratedComponentClock U h :=
    funext (nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh)
  intro j
  change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedCrossEdgeLabels U e f c)
      (j+1)).value (nativeStreamingGeneratedCrossEdgeAppend h r l) ≤
    (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedCrossEdgeLabels U e f c)
      j).value (nativeStreamingGeneratedCrossEdgeAppend h r l)
  simp only [nativeStreamingGeneratedCrossEdgeLabels_global,
    nativeStreamingGeneratedCrossEdgeGlobalLabels_append U e f c h r l hc, hq]
  exact nativeStreamingPairObservationSchedule_antitone _
    (nativeStreamingGeneratedComponentClock_antitone U h) e.depth f.depth r l hr hl (Nat.le_succ j.val)

def printedGeneratedEndpointCrossVertexComponent
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree) :
    CavityGeneratedConstructedComponent (m+2) :=
  nativeStreamingGeneratedCrossVertexComponent (nativeStreamingGeneratedEndpointComponent U)
    (nativeStreamingGeneratedEndpointVertex U v) (nativeStreamingGeneratedEndpointVertex U w)
    (nativeStreamingGeneratedEndpointVertex_interior U v).1
    (nativeStreamingGeneratedEndpointVertex_interior U v).2
    (nativeStreamingGeneratedEndpointVertex_interior U w).1
    (nativeStreamingGeneratedEndpointVertex_interior U w).2

def printedGeneratedEndpointMixedCrossComponent
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) : CavityGeneratedConstructedComponent (m+2) :=
  nativeStreamingGeneratedMixedCrossComponent (nativeStreamingGeneratedEndpointComponent U)
    (printedGeneratedEndpointEdge U e) (nativeStreamingGeneratedEndpointVertex U v)
    (nativeStreamingGeneratedEndpointVertex_interior U v).1
    (nativeStreamingGeneratedEndpointVertex_interior U v).2

theorem printedGeneratedEndpointCrossVertex_order
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))
      (nativeStreamingGeneratedComponentClock U h w.depth) ∈
        nativeStreamingGeneratedComponentOrderSet (printedGeneratedEndpointCrossVertexComponent U v w) := by
  have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
    rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
  have H := printedGeneratedCrossVertex_order (nativeStreamingGeneratedEndpointComponent U)
    (nativeStreamingGeneratedEndpointVertex U v) (nativeStreamingGeneratedEndpointVertex U w)
    (nativeStreamingGeneratedEndpointVertex_interior U v).1
    (nativeStreamingGeneratedEndpointVertex_interior U v).2
    (nativeStreamingGeneratedEndpointVertex_interior U w).1
    (nativeStreamingGeneratedEndpointVertex_interior U w).2 h hp
  rw [nativeStreamingGeneratedEndpointVertex_clock, nativeStreamingGeneratedEndpointVertex_clock] at H
  exact H

theorem printedGeneratedEndpointMixedCross_order
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth) :
    Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth) ∈
      nativeStreamingGeneratedComponentOrderSet (printedGeneratedEndpointMixedCrossComponent U e v) := by
  have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
    rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
  have H := printedGeneratedMixedCross_order (nativeStreamingGeneratedEndpointComponent U)
    (printedGeneratedEndpointEdge U e) (nativeStreamingGeneratedEndpointVertex U v)
    (nativeStreamingGeneratedEndpointVertex_interior U v).1
    (nativeStreamingGeneratedEndpointVertex_interior U v).2 h r hp
    (printedGeneratedEndpointEdge_cell U e h r hr)
  rw [nativeStreamingGeneratedEndpointVertex_clock] at H
  exact H

def printedGeneratedOriginCrossChartComponent
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (c : NativeStreamingGeneratedCrossEdgeChart) : CavityGeneratedConstructedComponent (m+2) :=
  match γ₁, γ₂ with
  | .inl i, .inl j => nativeStreamingGeneratedCrossVertexComponent U
      (printedGeneratedOriginChartFork U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  | .inr (.inl i), .inl j => nativeStreamingGeneratedMixedCrossComponent U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  | .inl i, .inr (.inl j) => printedGeneratedCrossSwapComponent
      (nativeStreamingGeneratedMixedCrossComponent U
        (printedGeneratedOriginChartEdge U j) (printedGeneratedOriginChartFork U i)
        (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2)
  | .inr (.inl i), .inr (.inl j) => nativeStreamingGeneratedCrossEdgeComponent U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartEdge U j) c
  | .inr (.inr _), .inl j => printedGeneratedEndpointCrossVertexComponent U
      (.root U.tree) (printedGeneratedOriginChartFork U j)
  | .inl i, .inr (.inr _) => printedGeneratedEndpointCrossVertexComponent U
      (printedGeneratedOriginChartFork U i) (.root U.tree)
  | .inr (.inr _), .inr (.inl j) => printedGeneratedCrossSwapComponent
      (printedGeneratedEndpointMixedCrossComponent U (printedGeneratedOriginChartEdge U j) (.root U.tree))
  | .inr (.inl i), .inr (.inr _) => printedGeneratedEndpointMixedCrossComponent U
      (printedGeneratedOriginChartEdge U i) (.root U.tree)
  | .inr (.inr _), .inr (.inr _) => printedGeneratedEndpointCrossVertexComponent U
      (.root U.tree) (.root U.tree)

def printedGeneratedOriginCrossChartHolds
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (c : NativeStreamingGeneratedCrossEdgeChart) (r l : Paper.Overlap) : Prop :=
  match γ₁, γ₂ with
  | .inr (.inl i), .inr (.inl j) =>
      c.Holds (printedGeneratedOriginChartEdge U i).depth (printedGeneratedOriginChartEdge U j).depth r l
  | _, _ => True

def printedGeneratedOriginCrossChartAppend
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap) :
    CavityGeneratedHistory Paper.Overlap (m+2) :=
  Fin.snoc (Fin.snoc h (printedGeneratedOriginChartClock U γ₁ h r))
    (printedGeneratedOriginChartClock U γ₂ h l)

theorem printedGeneratedOriginCrossChartComponent_order
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r)
    (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hc : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ c r l) :
    printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l ∈
      nativeStreamingGeneratedComponentOrderSet (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ c) := by
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  · exact printedGeneratedCrossVertex_order U _ _
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2 h hh
  · exact printedGeneratedCrossSwapComponent_order _ h
      (nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartFork U i).depth) l
      (printedGeneratedMixedCross_order U (printedGeneratedOriginChartEdge U j)
        (printedGeneratedOriginChartFork U i)
        (printedGeneratedOriginChartFork_interior U i).1
        (printedGeneratedOriginChartFork_interior U i).2 h l hh hl)
  · exact printedGeneratedEndpointCrossVertex_order U _ (.root U.tree) h hh
  · exact printedGeneratedMixedCross_order U _ _
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2 h r hh hr
  · exact printedGeneratedCrossEdge_order U _ _ c h r l hh hr hl hc
  · exact printedGeneratedEndpointMixedCross_order U _ (.root U.tree) h r hh hr
  · exact printedGeneratedEndpointCrossVertex_order U (.root U.tree) _ h hh
  · exact printedGeneratedCrossSwapComponent_order _ h
      (nativeStreamingGeneratedComponentClock U h U.depth) l
      (printedGeneratedEndpointMixedCross_order U (printedGeneratedOriginChartEdge U j)
        (.root U.tree) h l hh hl)
  · exact printedGeneratedEndpointCrossVertex_order U (.root U.tree) (.root U.tree) h hh

theorem printedGeneratedCrossVertex_leafCount
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (hw0 : 0 < w.depth) (hwJ : w.depth < U.depth) :
    cavityGeneratedComponentLeafCount (nativeStreamingGeneratedCrossVertexComponent U v w hv0 hvJ hw0 hwJ) =
      cavityGeneratedComponentLeafCount U + 2 := by
  unfold nativeStreamingGeneratedCrossVertexComponent
  rw [printedGeneratedVertexComponent_leafCount, printedGeneratedVertexComponent_leafCount]
  simp only [NativeStreamingGeneratedVertexKind.newLeafCount]

theorem printedGeneratedMixedCross_leafCount
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) :
    cavityGeneratedComponentLeafCount (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ) =
      cavityGeneratedComponentLeafCount U + 2 := by
  unfold nativeStreamingGeneratedMixedCrossComponent
  rw [printedGeneratedVertexComponent_leafCount, printedGeneratedEdgeComponent_leafCount]
  simp only [NativeStreamingGeneratedVertexKind.newLeafCount]

theorem printedGeneratedCrossEdge_leafCount
    (U : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge U.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    cavityGeneratedComponentLeafCount (nativeStreamingGeneratedCrossEdgeComponent U e f c) =
      cavityGeneratedComponentLeafCount U + 2 := by
  change FiniteCascadeGenealogy.leafCount (asGenealogy
    (finiteCascadeCrossContinuationGraft observationLinearTree
      (nativeStreamingGeneratedCrossEdgeFirstVertex U e f c)
      (nativeStreamingGeneratedCrossEdgeSecondVertex U e f c))) = _
  change FiniteCascadeGenealogy.leafCount (asGenealogy
    (finiteCascadeContinuationGraft observationLinearTree
      (finiteCascadeContinuationVertexEmbed observationLinearTree
        (nativeStreamingGeneratedCrossEdgeFirstVertex U e f c)
        (nativeStreamingGeneratedCrossEdgeSecondVertex U e f c)))) = _
  rw [finiteCascadeContinuationGraft_leafCount, printedGeneratedLinearTree_leafCount,
    finiteCascadeContinuationGraft_leafCount, printedGeneratedLinearTree_leafCount]
  change FiniteCascadeGenealogy.leafCount (asGenealogy
    (observationRefineTree nativeStreamingPairObservationSubdivision U.tree)) + 1 + 1 = _
  rw [printedGeneratedRefinement_leafCount]
  change cavityGeneratedComponentLeafCount U + 1 + 1 = _
  omega

theorem printedGeneratedOriginCrossChartComponent_leafCount
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    cavityGeneratedComponentLeafCount (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ c) =
      cavityGeneratedComponentLeafCount U + 2 := by
  have hvv : ∀v w : FiniteCascadeRecordVertex U.tree,
      cavityGeneratedComponentLeafCount (printedGeneratedEndpointCrossVertexComponent U v w) =
        cavityGeneratedComponentLeafCount U + 2 := by
    intro v w
    unfold printedGeneratedEndpointCrossVertexComponent
    rw [printedGeneratedCrossVertex_leafCount, printedGeneratedEndpointComponent_leafCount]
  have hev : ∀e : NativeStreamingEdge U.tree, ∀v : FiniteCascadeRecordVertex U.tree,
      cavityGeneratedComponentLeafCount (printedGeneratedEndpointMixedCrossComponent U e v) =
        cavityGeneratedComponentLeafCount U + 2 := by
    intro e v
    unfold printedGeneratedEndpointMixedCrossComponent
    rw [printedGeneratedMixedCross_leafCount, printedGeneratedEndpointComponent_leafCount]
  have hs : ∀A : CavityGeneratedConstructedComponent (m+2),
      cavityGeneratedComponentLeafCount (printedGeneratedCrossSwapComponent A) =
        cavityGeneratedComponentLeafCount A := by
    intro A
    rfl
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  · exact printedGeneratedCrossVertex_leafCount U _ _
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  · change cavityGeneratedComponentLeafCount (printedGeneratedCrossSwapComponent _) = _
    rw [hs]
    exact printedGeneratedMixedCross_leafCount U _ _
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
  · exact hvv (printedGeneratedOriginChartFork U i) (.root U.tree)
  · exact printedGeneratedMixedCross_leafCount U _ _
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  · exact printedGeneratedCrossEdge_leafCount U _ _ c
  · exact hev (printedGeneratedOriginChartEdge U i) (.root U.tree)
  · exact hvv (.root U.tree) (printedGeneratedOriginChartFork U j)
  · change cavityGeneratedComponentLeafCount (printedGeneratedCrossSwapComponent _) = _
    rw [hs]
    exact hev (printedGeneratedOriginChartEdge U j) (.root U.tree)
  · exact hvv (.root U.tree) (.root U.tree)

end QuantitativeFollowup
