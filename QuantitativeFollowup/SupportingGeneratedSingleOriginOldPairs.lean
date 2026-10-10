module
public import QuantitativeFollowup.SupportingGeneratedOriginComponentReceivers
public import QuantitativeFollowup.SupportingGeneratedEndpointOldPairs

@[expose] public section

/-! The single-origin charts retain every original terminal leaf.  Its
terminal spin and every original pair's physical common clock are unchanged,
including diagonal pairs and the padded root chart. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem nativeStreamingGeneratedContinuationTerminalMap_old_leaf {S : Type}
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) (i : ObservationLeaf T)
    (σ : TerminalSpins S (finiteCascadeContinuationGraft U v)) :
    observationTerminalSpin T i (nativeStreamingGeneratedContinuationTerminalMap U v σ).1 =
      observationTerminalSpin (finiteCascadeContinuationGraft U v)
        (finiteCascadeContinuationOldLeaf U v i) σ := by
  induction v with
  | root T => rfl
  | child v ih => exact ih i σ
  | left v ih =>
      cases i with
      | inl i => exact ih i σ.1
      | inr i => rfl
  | right v ih =>
      cases i with
      | inl i => rfl
      | inr i => exact ih i σ.2

theorem nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf {S : Type}
    (k : NativeStreamingGeneratedVertexKind) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) (i : ObservationLeaf T)
    (σ : TerminalSpins S (finiteCascadeContinuationGraft k.continuation v)) :
    observationTerminalSpin T i (nativeStreamingGeneratedVertexTerminalProjection k v σ).1 =
      observationTerminalSpin (finiteCascadeContinuationGraft k.continuation v)
        (finiteCascadeContinuationOldLeaf k.continuation v i) σ :=
  nativeStreamingGeneratedContinuationTerminalMap_old_leaf k.continuation v i σ

def printedGeneratedOriginChartOldLeaf (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (k : NativeStreamingGeneratedVertexKind)
    (i : ObservationLeaf U.tree) :
    ObservationLeaf (printedGeneratedOriginChartComponent U γ k).tree :=
  match γ with
  | .inl j => finiteCascadeContinuationOldLeaf k.continuation (printedGeneratedOriginChartFork U j) i
  | .inr (.inl j) => finiteCascadeContinuationOldLeaf k.continuation
      (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U j))
      (nativeStreamingGeneratedEdgeLeaf U (printedGeneratedOriginChartEdge U j) i)
  | .inr (.inr _) => finiteCascadeContinuationOldLeaf k.continuation
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointLeaf U i)

theorem printedGeneratedOriginChartTerminalProject_old_leaf
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (i : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ k)) :
    observationTerminalSpin U.tree i (printedGeneratedOriginChartTerminalProject U γ k σ).1 =
      observationTerminalSpin (printedGeneratedOriginChartComponent U γ k).tree
        (printedGeneratedOriginChartOldLeaf U γ k i) σ := by
  rcases γ with j | (j | u)
  · exact nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf k _ i σ
  · change observationTerminalSpin U.tree i
      (nativeStreamingGeneratedEdgeTerminalProject U (printedGeneratedOriginChartEdge U j)
        (nativeStreamingGeneratedVertexTerminalProjection k
          (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U j)) σ).1) = _
    rw [nativeStreamingGeneratedEdgeTerminalProject_leaf]
    exact nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf k _ _ σ
  · change observationTerminalSpin U.tree i
      (nativeStreamingGeneratedEndpointTerminalProject U
        (nativeStreamingGeneratedVertexTerminalProjection k
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree)) σ).1) = _
    rw [nativeStreamingGeneratedEndpointTerminalProject_leaf]
    exact nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf k _ _ σ

theorem printedGeneratedOriginChartOldLeaves_commonClock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) (i j : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ k)
      (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
      (observationCommonLevel (printedGeneratedOriginChartComponent U γ k).tree
        (printedGeneratedOriginChartOldLeaf U γ k i) (printedGeneratedOriginChartOldLeaf U γ k j)) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j) := by
  rcases γ with v | (e | u)
  · change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedVertexComponent U (printedGeneratedOriginChartFork U v)
        (printedGeneratedOriginChartFork_interior U v).1
        (printedGeneratedOriginChartFork_interior U v).2 k)
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartFork U v).depth))
      (observationCommonLevel _ (finiteCascadeContinuationOldLeaf k.continuation _ i)
        (finiteCascadeContinuationOldLeaf k.continuation _ j)) = _
    rw [finiteCascadeContinuationOldLeaf_commonLevel,
      printedGeneratedVertexComponent_snoc_clock U _ _ _ k h hh]
  · change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedEdgeComponent U (printedGeneratedOriginChartEdge U e) k) (Fin.snoc h r)
      (observationCommonLevel _
        (finiteCascadeContinuationOldLeaf k.continuation _
          (nativeStreamingGeneratedEdgeLeaf U (printedGeneratedOriginChartEdge U e) i))
        (finiteCascadeContinuationOldLeaf k.continuation _
          (nativeStreamingGeneratedEdgeLeaf U (printedGeneratedOriginChartEdge U e) j))) = _
    rw [finiteCascadeContinuationOldLeaf_commonLevel,
      nativeStreamingGeneratedEdgeComponent_clock,
      nativeStreamingGeneratedEdgeObservedComponent_clock_snoc U _ h r hh hr]
    change nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h)
      (printedGeneratedOriginChartEdge U e).depth r
      (observationCommonLevel _ (observationRefinementLeafEmbed _ U.tree i)
        (observationRefinementLeafEmbed _ U.tree j)) = _
    rw [observationRefinementLeafEmbed_commonLevel,nativeStreamingEdgeSchedule_refinement]
  · have hhp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have hs := printedGeneratedVertexComponent_snoc_clock (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 k h hhp
    rw [nativeStreamingGeneratedEndpointVertex_clock] at hs
    change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedVertexComponent (nativeStreamingGeneratedEndpointComponent U)
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 k)
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h U.depth))
      (observationCommonLevel _
        (finiteCascadeContinuationOldLeaf k.continuation _ (nativeStreamingGeneratedEndpointLeaf U i))
        (finiteCascadeContinuationOldLeaf k.continuation _ (nativeStreamingGeneratedEndpointLeaf U j))) = _
    rw [finiteCascadeContinuationOldLeaf_commonLevel,hs]
    exact nativeStreamingGeneratedEndpointOldLeaves_commonClock U h i j

theorem printedGeneratedOriginChartOldPair_defect
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) (i j : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ k)) :
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j))
      (observationTerminalSpin U.tree i (printedGeneratedOriginChartTerminalProject U γ k σ).1)
      (observationTerminalSpin U.tree j (printedGeneratedOriginChartTerminalProject U γ k σ).1) =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ k)
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
        (observationCommonLevel (printedGeneratedOriginChartComponent U γ k).tree
          (printedGeneratedOriginChartOldLeaf U γ k i) (printedGeneratedOriginChartOldLeaf U γ k j)))
      (observationTerminalSpin _ (printedGeneratedOriginChartOldLeaf U γ k i) σ)
      (observationTerminalSpin _ (printedGeneratedOriginChartOldLeaf U γ k j) σ) := by
  rw [printedGeneratedOriginChartOldLeaves_commonClock U γ k h r hh hr,
    printedGeneratedOriginChartTerminalProject_old_leaf,
    printedGeneratedOriginChartTerminalProject_old_leaf]

end QuantitativeFollowup
