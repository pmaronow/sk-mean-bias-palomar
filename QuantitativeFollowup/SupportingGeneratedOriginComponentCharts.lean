module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionLocations
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsGeometry
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsOrder
public import QuantitativeFollowup.SupportingGeneratedForestLeafCounts

@[expose] public section

/-! A selected original fork, edge, or root determines an actual constructed
component. Only the edge payload is a free clock. The ordering event comes
from the original component and the selected cell, and leaf growth is read
from the constructed genealogy. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m J : ℕ}

def PrintedGeneratedOriginChart (U : CavityGeneratedConstructedComponent m) :=
  Fin (cavityGeneratedOriginForkVertices U.tree).length ⊕
    (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)

def printedGeneratedOriginChartFork (U : CavityGeneratedConstructedComponent m)
    (i : Fin (cavityGeneratedOriginForkVertices U.tree).length) :
    FiniteCascadeRecordVertex U.tree := (cavityGeneratedOriginForkVertices U.tree).get i

def printedGeneratedOriginChartEdge (U : CavityGeneratedConstructedComponent m)
    (i : Fin (cavityGeneratedOriginEdges U.tree).length) : NativeStreamingEdge U.tree :=
  (cavityGeneratedOriginEdges U.tree).get i

theorem printedGeneratedOriginChartFork_interior (U : CavityGeneratedConstructedComponent m)
    (i : Fin (cavityGeneratedOriginForkVertices U.tree).length) :
    0 < (printedGeneratedOriginChartFork U i).depth ∧
      (printedGeneratedOriginChartFork U i).depth < U.depth := by
  let v := printedGeneratedOriginChartFork U i
  have hv : v ∈ cavityGeneratedOriginForkVertices U.tree := List.get_mem _ i
  obtain ⟨j,hj⟩ := cavityGeneratedOriginForkVertex_mark
    (nativeStreamingGeneratedComponentForest U) (0 : Fin 1) v hv
  change cavityGeneratedFiniteClockLabels U.label v.depth = .mark j at hj
  have hd := v.depth_le
  have hn0 : v.depth ≠ 0 := by
    intro he
    rw [he] at hj
    have ht : cavityGeneratedFiniteClockLabels U.label 0 = .terminal := by
      simp only [cavityGeneratedFiniteClockLabels, Nat.zero_le, dif_pos]
      exact U.terminal_label
    rw [ht] at hj
    cases hj
  have hnJ : v.depth ≠ U.depth := by
    intro he
    rw [he] at hj
    have ht : cavityGeneratedFiniteClockLabels U.label U.depth = .initial := by
      simp only [cavityGeneratedFiniteClockLabels, dif_pos le_rfl]
      exact U.initial_label
    rw [ht] at hj
    cases hj
  change 0 < v.depth ∧ v.depth < U.depth
  omega

def printedGeneratedOriginChartClock (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) : Paper.Overlap := match γ with
  | .inl i => nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartFork U i).depth
  | .inr (.inl _) => r
  | .inr (.inr _) => nativeStreamingGeneratedComponentClock U h U.depth

def printedGeneratedOriginChartComponent (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedConstructedComponent (m+1) := match γ with
  | .inl i => nativeStreamingGeneratedVertexComponent U (printedGeneratedOriginChartFork U i)
      (printedGeneratedOriginChartFork_interior U i).1
      (printedGeneratedOriginChartFork_interior U i).2 k
  | .inr (.inl i) => nativeStreamingGeneratedEdgeComponent U (printedGeneratedOriginChartEdge U i) k
  | .inr (.inr _) => nativeStreamingGeneratedVertexComponent
      (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 k

def printedGeneratedOriginChartCell (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) : Prop := match γ with
  | .inl _ => True
  | .inr (.inl i) =>
      nativeStreamingGeneratedComponentClock U h ((printedGeneratedOriginChartEdge U i).depth+1) ≤ r ∧
        r ≤ nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartEdge U i).depth
  | .inr (.inr _) => True

theorem printedGeneratedVertexComponent_snoc_raw
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (k : NativeStreamingGeneratedVertexKind)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) (j : ℕ) :
    (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedVertexComponent U v hv0 hvJ k).label j).value
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)) =
        nativeStreamingGeneratedComponentClock U h j := by
  change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedVertexLabels U v.depth) j).value _ = _
  rw [nativeStreamingGeneratedVertexLabels_global U v.depth hvJ.le]
  unfold cavityGeneratedAttachedClockLabels
  by_cases he : j = v.depth
  · subst j
    simp only [ite_true, CavityGeneratedClockLabel.value, Fin.snoc_last]
  · rw [if_neg he, CavityGeneratedClockLabel.append_reindex_value,
      cavityGeneratedHistoryPrefix_snoc]
    exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh j

theorem printedGeneratedVertexComponent_snoc_order
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (k : NativeStreamingGeneratedVertexKind)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth) ∈
      nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedVertexComponent U v hv0 hvJ k) := by
  intro j
  rw [printedGeneratedVertexComponent_snoc_raw U v hv0 hvJ k h hh,
    printedGeneratedVertexComponent_snoc_raw U v hv0 hvJ k h hh]
  exact nativeStreamingGeneratedComponentClock_antitone U h (Nat.le_succ j.val)

theorem printedGeneratedEdgeComponent_snoc_order
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth) :
    Fin.snoc h r ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEdgeComponent U e k) := by
  have he : ∀j, (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeComponent U e k).label j).value
      (Fin.snoc h r) = nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h) e.depth r j := by
    intro j
    change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels U e) j).value _ = _
    rw [nativeStreamingGeneratedEdgeLabels_global,nativeStreamingGeneratedEdgeGlobalLabels_snoc_value]
    congr 1
    funext p
    exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh p
  intro j
  rw [he,he]
  exact nativeStreamingEdgeSchedule_antitone _ (nativeStreamingGeneratedComponentClock_antitone U h)
    e.depth r hr (Nat.le_succ j.val)

theorem printedGeneratedOriginChartComponent_snoc_order
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) :
    Fin.snoc h (printedGeneratedOriginChartClock U γ h r) ∈
      nativeStreamingGeneratedComponentOrderSet (printedGeneratedOriginChartComponent U γ k) := by
  rcases γ with i | (i | u)
  · exact printedGeneratedVertexComponent_snoc_order U (printedGeneratedOriginChartFork U i)
      (printedGeneratedOriginChartFork_interior U i).1
      (printedGeneratedOriginChartFork_interior U i).2 k h hh
  · exact printedGeneratedEdgeComponent_snoc_order U _ k h r hh hr
  · have hhp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have ho := printedGeneratedVertexComponent_snoc_order (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 k h hhp
    rw [nativeStreamingGeneratedEndpointVertex_clock] at ho
    exact ho

def NativeStreamingGeneratedVertexKind.newLeafCount : NativeStreamingGeneratedVertexKind → ℕ
  | .single => 1
  | .current => 2

theorem printedGeneratedLinearTree_leafCount (j : ℕ) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (observationLinearTree j)) = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem printedGeneratedContinuation_leafCount (k : NativeStreamingGeneratedVertexKind) (j : ℕ) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (k.continuation j)) = k.newLeafCount := by
  cases k with
  | single => exact printedGeneratedLinearTree_leafCount j
  | current =>
      change FiniteCascadeGenealogy.leafCount (asGenealogy (observationLinearTree j)) +
        FiniteCascadeGenealogy.leafCount (asGenealogy (observationLinearTree j)) = 2
      rw [printedGeneratedLinearTree_leafCount]

theorem printedGeneratedTreePad_leafCount (T : FiniteTerminalGenealogy J) (d : ℕ) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (observationTreePad T d)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem printedGeneratedRefinement_leafCount (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (observationRefineTree d T)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction T with
  | leaf => rfl
  | advance T ih => exact (printedGeneratedTreePad_leafCount _ _).trans ih
  | fork T V ihT ihV =>
      change FiniteCascadeGenealogy.leafCount (asGenealogy (observationRefineTree d T)) +
        FiniteCascadeGenealogy.leafCount (asGenealogy (observationRefineTree d V)) = _
      rw [ihT,ihV]
      rfl

theorem printedGeneratedEndpointLift_leafCount (T : FiniteTerminalGenealogy J) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (observationTerminalUnaryLift T)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih
  | fork T V ihT ihV =>
      change FiniteCascadeGenealogy.leafCount (asGenealogy (observationTerminalUnaryLift T)) +
        FiniteCascadeGenealogy.leafCount (asGenealogy (observationTerminalUnaryLift V)) = _
      rw [ihT,ihV]
      rfl

theorem printedGeneratedVertexComponent_leafCount
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (k : NativeStreamingGeneratedVertexKind) :
    cavityGeneratedComponentLeafCount (nativeStreamingGeneratedVertexComponent U v hv0 hvJ k) =
      cavityGeneratedComponentLeafCount U + k.newLeafCount := by
  change FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeContinuationGraft k.continuation v)) = _
  rw [finiteCascadeContinuationGraft_leafCount,printedGeneratedContinuation_leafCount]
  rfl

theorem printedGeneratedEdgeComponent_leafCount
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedVertexKind) :
    cavityGeneratedComponentLeafCount (nativeStreamingGeneratedEdgeComponent U e k) =
      cavityGeneratedComponentLeafCount U + k.newLeafCount := by
  change FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeContinuationGraft k.continuation
    (nativeStreamingGeneratedEdgeVertex U e))) = _
  rw [finiteCascadeContinuationGraft_leafCount,printedGeneratedContinuation_leafCount]
  change FiniteCascadeGenealogy.leafCount (asGenealogy (observationRefineTree
    (nativeStreamingEdgeSubdivision e.depth) U.tree)) + k.newLeafCount = _
  rw [printedGeneratedRefinement_leafCount]
  rfl

theorem printedGeneratedEndpointComponent_leafCount (U : CavityGeneratedConstructedComponent m) :
    cavityGeneratedComponentLeafCount (nativeStreamingGeneratedEndpointComponent U) =
      cavityGeneratedComponentLeafCount U := printedGeneratedEndpointLift_leafCount U.tree

theorem printedGeneratedOriginChartComponent_leafCount
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) :
    cavityGeneratedComponentLeafCount (printedGeneratedOriginChartComponent U γ k) =
      cavityGeneratedComponentLeafCount U + k.newLeafCount := by
  rcases γ with i | (i | u)
  · exact printedGeneratedVertexComponent_leafCount U (printedGeneratedOriginChartFork U i)
      (printedGeneratedOriginChartFork_interior U i).1
      (printedGeneratedOriginChartFork_interior U i).2 k
  · exact printedGeneratedEdgeComponent_leafCount U _ k
  · rw [printedGeneratedOriginChartComponent,printedGeneratedVertexComponent_leafCount,
      printedGeneratedEndpointComponent_leafCount]

theorem printedGeneratedOriginChartComponent_leafCount_le
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) :
    cavityGeneratedComponentLeafCount (printedGeneratedOriginChartComponent U γ k) ≤
      cavityGeneratedComponentLeafCount U + 2 := by
  rw [printedGeneratedOriginChartComponent_leafCount]
  cases k <;> simp only [NativeStreamingGeneratedVertexKind.newLeafCount] <;> omega

end QuantitativeFollowup
