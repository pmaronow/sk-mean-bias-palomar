module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverClocks
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossEdgePatternsLaw

@[expose] public section

/-! The two cross-source spins are the actual fresh terminal leaves of the
computed chart tree. Their common level carries the original physical clock,
including padded roots, reversed mixed charts, and coincident origins. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def printedGeneratedMixedCrossFirstLeaf
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0<v.depth) (hvJ : v.depth<U.depth) :
    ObservationLeaf (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ).tree :=
  finiteCascadeLinearCrossFirstLeaf (nativeStreamingGeneratedEdgeVertex U e)
    (nativeStreamingGeneratedMixedRefinedVertex U e v)

def printedGeneratedMixedCrossSecondLeaf
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0<v.depth) (hvJ : v.depth<U.depth) :
    ObservationLeaf (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ).tree :=
  finiteCascadeLinearCrossSecondLeaf (nativeStreamingGeneratedEdgeVertex U e)
    (nativeStreamingGeneratedMixedRefinedVertex U e v)

def printedGeneratedOriginCrossChartFirstLeaf
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    ObservationLeaf (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree :=
  match γ₁,γ₂ with
  | .inl i,.inl j => finiteCascadeLinearCrossFirstLeaf
      (printedGeneratedOriginChartFork U i) (printedGeneratedOriginChartFork U j)
  | .inr (.inl i),.inl j => printedGeneratedMixedCrossFirstLeaf U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  | .inl i,.inr (.inl j) => printedGeneratedMixedCrossSecondLeaf U
      (printedGeneratedOriginChartEdge U j) (printedGeneratedOriginChartFork U i)
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
  | .inr (.inl i),.inr (.inl j) => finiteCascadeLinearCrossFirstLeaf
      (nativeStreamingGeneratedCrossEdgeFirstVertex U (printedGeneratedOriginChartEdge U i)
        (printedGeneratedOriginChartEdge U j) k)
      (nativeStreamingGeneratedCrossEdgeSecondVertex U (printedGeneratedOriginChartEdge U i)
        (printedGeneratedOriginChartEdge U j) k)
  | .inr (.inr _),.inl j => finiteCascadeLinearCrossFirstLeaf
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U j))
  | .inl i,.inr (.inr _) => finiteCascadeLinearCrossFirstLeaf
      (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U i))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
  | .inr (.inl i),.inr (.inr _) => printedGeneratedMixedCrossFirstLeaf
      (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U i))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inr _),.inr (.inl j) => printedGeneratedMixedCrossSecondLeaf
      (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U j))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inr _),.inr (.inr _) => finiteCascadeLinearCrossFirstLeaf
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))

def printedGeneratedOriginCrossChartSecondLeaf
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    ObservationLeaf (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree :=
  match γ₁,γ₂ with
  | .inl i,.inl j => finiteCascadeLinearCrossSecondLeaf
      (printedGeneratedOriginChartFork U i) (printedGeneratedOriginChartFork U j)
  | .inr (.inl i),.inl j => printedGeneratedMixedCrossSecondLeaf U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  | .inl i,.inr (.inl j) => printedGeneratedMixedCrossFirstLeaf U
      (printedGeneratedOriginChartEdge U j) (printedGeneratedOriginChartFork U i)
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
  | .inr (.inl i),.inr (.inl j) => finiteCascadeLinearCrossSecondLeaf
      (nativeStreamingGeneratedCrossEdgeFirstVertex U (printedGeneratedOriginChartEdge U i)
        (printedGeneratedOriginChartEdge U j) k)
      (nativeStreamingGeneratedCrossEdgeSecondVertex U (printedGeneratedOriginChartEdge U i)
        (printedGeneratedOriginChartEdge U j) k)
  | .inr (.inr _),.inl j => finiteCascadeLinearCrossSecondLeaf
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U j))
  | .inl i,.inr (.inr _) => finiteCascadeLinearCrossSecondLeaf
      (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U i))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
  | .inr (.inl i),.inr (.inr _) => printedGeneratedMixedCrossSecondLeaf
      (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U i))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inr _),.inr (.inl j) => printedGeneratedMixedCrossFirstLeaf
      (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U j))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inr _),.inr (.inr _) => finiteCascadeLinearCrossSecondLeaf
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))

private theorem vertexFreshClock
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<U.depth) (hw0 : 0<w.depth) (hwJ : w.depth<U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedCrossVertexComponent U v w hv0 hvJ hw0 hwJ)
      (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))
        (nativeStreamingGeneratedComponentClock U h w.depth))
      (observationCommonLevel _ (finiteCascadeLinearCrossFirstLeaf v w)
        (finiteCascadeLinearCrossSecondLeaf v w)) =
      nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (.vertex v) (.vertex w) := by
  rw [←printedGeneratedCrossVertexAppend_physical U v w h hh,
    nativeStreamingGeneratedCrossVertexComponent_clock_append,
    finiteCascadeLinearCrossFresh_commonLevel]
  rfl

private theorem mixedFreshClock
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0<v.depth) (hvJ : v.depth<U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock U h e.depth) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ)
      (Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth))
      (observationCommonLevel _ (printedGeneratedMixedCrossFirstLeaf U e v hv0 hvJ)
        (printedGeneratedMixedCrossSecondLeaf U e v hv0 hvJ)) =
      nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (.edge e r) (.vertex v) := by
  rw [printedGeneratedMixedCrossClock_physical U e v hv0 hvJ h r hh hr]
  change nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h) e.depth r
    (observationCommonLevel _
      (finiteCascadeLinearCrossFirstLeaf (nativeStreamingGeneratedEdgeVertex U e)
        (nativeStreamingGeneratedMixedRefinedVertex U e v))
      (finiteCascadeLinearCrossSecondLeaf (nativeStreamingGeneratedEdgeVertex U e)
        (nativeStreamingGeneratedMixedRefinedVertex U e v))) = _
  rw [finiteCascadeLinearCrossFresh_commonLevel]
  exact nativeStreamingGeneratedMixedCross_common_clock U e v _ r

private theorem endpointRootLeftClock
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex U.tree) :
    nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedEndpointComponent U) h) (nativeStreamingGeneratedEndpointComponent U).tree
      (.vertex (nativeStreamingGeneratedEndpointVertex U (.root U.tree)))
      (.vertex (nativeStreamingGeneratedEndpointVertex U v)) =
    nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
      (.vertex (.root U.tree)) (.vertex v) := by
  change nativeStreamingGeneratedEndpointClock U h
    (finiteCascadeCommonPathDepth (observationTerminalUnaryLift U.tree)
      (.root _) (nativeStreamingEndpointLiftVertex v)) =
    nativeStreamingGeneratedComponentClock U h (finiteCascadeCommonPathDepth U.tree (.root _) v)
  rw [finiteCascadeCommonPathDepth_root_left, finiteCascadeCommonPathDepth_root_left,
    nativeStreamingGeneratedEndpointClock_succ]

private theorem endpointRootRightClock
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex U.tree) :
    nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedEndpointComponent U) h) (nativeStreamingGeneratedEndpointComponent U).tree
      (.vertex (nativeStreamingGeneratedEndpointVertex U v))
      (.vertex (nativeStreamingGeneratedEndpointVertex U (.root U.tree))) =
    nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
      (.vertex v) (.vertex (.root U.tree)) := by
  change nativeStreamingGeneratedEndpointClock U h
    (finiteCascadeCommonPathDepth (observationTerminalUnaryLift U.tree)
      (nativeStreamingEndpointLiftVertex v) (.root _)) =
    nativeStreamingGeneratedComponentClock U h (finiteCascadeCommonPathDepth U.tree v (.root _))
  rw [finiteCascadeCommonPathDepth_root_right, finiteCascadeCommonPathDepth_root_right,
    nativeStreamingGeneratedEndpointClock_succ]

private theorem endpointRootMixedClock
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (e : NativeStreamingEdge U.tree) (r : Paper.Overlap) :
    nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedEndpointComponent U) h) (nativeStreamingGeneratedEndpointComponent U).tree
      (.edge (printedGeneratedEndpointEdge U e) r)
      (.vertex (nativeStreamingGeneratedEndpointVertex U (.root U.tree))) =
    nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
      (.edge e r) (.vertex (.root U.tree)) := by
  have hc : finiteCascadeCommonPathDepth (nativeStreamingGeneratedEndpointComponent U).tree
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingEdgeChildVertex (printedGeneratedEndpointEdge U e)) = U.depth+1 := by
    change finiteCascadeCommonPathDepth (observationTerminalUnaryLift U.tree)
      (.root _) (nativeStreamingEdgeChildVertex (printedGeneratedEndpointLiftEdge e)) = _
    exact finiteCascadeCommonPathDepth_root_left _ _
  have he : U.depth ≠ e.depth := by have := e.depth_lt; omega
  have hep : U.depth+1 ≠ e.depth+1 := by omega
  simp only [nativeStreamingOriginCommonClock, hc, finiteCascadeCommonPathDepth_root_left,
    printedGeneratedEndpointEdge_depth, nativeStreamingGeneratedEndpointComponent_clock,
    nativeStreamingGeneratedEndpointClock_succ, nativeStreamingOldSelectedCommonClock,
    if_neg he, if_neg hep]

theorem printedGeneratedOriginCrossChart_fresh_common_clock
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r) (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
      (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l)
      (observationCommonLevel _ (printedGeneratedOriginCrossChartFirstLeaf U γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartSecondLeaf U γ₁ γ₂ k)) =
      nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (printedGeneratedOriginCrossChartOrigin U γ₁ r) (printedGeneratedOriginCrossChartOrigin U γ₂ l) := by
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  · exact vertexFreshClock U _ _
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2 h hh
  · change nativeStreamingGeneratedComponentClock (printedGeneratedCrossSwapComponent
        (nativeStreamingGeneratedMixedCrossComponent U
          (printedGeneratedOriginChartEdge U j) (printedGeneratedOriginChartFork U i)
          (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2))
      (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h
        (printedGeneratedOriginChartFork U i).depth)) l) (observationCommonLevel _
        (printedGeneratedMixedCrossSecondLeaf U (printedGeneratedOriginChartEdge U j)
          (printedGeneratedOriginChartFork U i)
          (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2)
        (printedGeneratedMixedCrossFirstLeaf U (printedGeneratedOriginChartEdge U j)
          (printedGeneratedOriginChartFork U i)
          (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2)) = _
    rw [printedGeneratedCrossSwapClock_append, cavityGenerated_observationCommonLevel_symm]
    exact mixedFreshClock U _ _
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2 h l hh hl
  · have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have H := vertexFreshClock (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U i))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U _).1 (nativeStreamingGeneratedEndpointVertex_interior U _).2
      (nativeStreamingGeneratedEndpointVertex_interior U _).1 (nativeStreamingGeneratedEndpointVertex_interior U _).2 h hp
    rw [nativeStreamingGeneratedEndpointVertex_clock, nativeStreamingGeneratedEndpointVertex_clock,
      endpointRootRightClock] at H
    exact H
  · exact mixedFreshClock U _ _
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2 h r hh hr
  · exact nativeStreamingGeneratedCrossEdge_common_clock U _ _ k h r l hh hr hl hk
  · have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have H := mixedFreshClock (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U i))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U _).1 (nativeStreamingGeneratedEndpointVertex_interior U _).2
      h r hp (printedGeneratedEndpointEdge_cell U _ h r hr)
    rw [nativeStreamingGeneratedEndpointVertex_clock, endpointRootMixedClock] at H
    exact H
  · have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have H := vertexFreshClock (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U j))
      (nativeStreamingGeneratedEndpointVertex_interior U _).1 (nativeStreamingGeneratedEndpointVertex_interior U _).2
      (nativeStreamingGeneratedEndpointVertex_interior U _).1 (nativeStreamingGeneratedEndpointVertex_interior U _).2 h hp
    rw [nativeStreamingGeneratedEndpointVertex_clock U h (.root U.tree),
      nativeStreamingGeneratedEndpointVertex_clock U h (printedGeneratedOriginChartFork U j),
      endpointRootLeftClock U h (printedGeneratedOriginChartFork U j)] at H
    exact H
  · let P := nativeStreamingGeneratedEndpointComponent U
    let e := printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U j)
    let w := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
    have hw := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
    change nativeStreamingGeneratedComponentClock (printedGeneratedCrossSwapComponent
        (nativeStreamingGeneratedMixedCrossComponent P e w hw.1 hw.2))
      (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h U.depth)) l)
      (observationCommonLevel _ (printedGeneratedMixedCrossSecondLeaf P e w hw.1 hw.2)
        (printedGeneratedMixedCrossFirstLeaf P e w hw.1 hw.2)) = _
    rw [printedGeneratedCrossSwapClock_append, cavityGenerated_observationCommonLevel_symm]
    have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have H := mixedFreshClock (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U j))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U _).1 (nativeStreamingGeneratedEndpointVertex_interior U _).2
      h l hp (printedGeneratedEndpointEdge_cell U _ h l hl)
    rw [nativeStreamingGeneratedEndpointVertex_clock, endpointRootMixedClock] at H
    exact H
  · have hp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have H := vertexFreshClock (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U _).1 (nativeStreamingGeneratedEndpointVertex_interior U _).2
      (nativeStreamingGeneratedEndpointVertex_interior U _).1 (nativeStreamingGeneratedEndpointVertex_interior U _).2 h hp
    rw [nativeStreamingGeneratedEndpointVertex_clock U h (.root U.tree),
      endpointRootLeftClock U h (.root U.tree)] at H
    exact H

end QuantitativeFollowup
