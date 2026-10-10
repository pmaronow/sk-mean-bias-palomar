module
public import QuantitativeFollowup.SupportingGeneratedCrossOriginOldPairClocks
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverTerminalProjection

@[expose] public section

/-! Literal old terminal spins and every previously marked pair defect
are preserved by each of the nine actual cross-source successor charts. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

private theorem mixedOldSpin {E S : Type}
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0<v.depth) (hvJ : v.depth<U.depth)
    (i : ObservationLeaf U.tree)
    (z : E × Records E S (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ).tree) :
    observationTerminalSpin U.tree i
      (printedGeneratedMixedCrossTerminalProjection U e v hv0 hvJ
        (finiteCascadeRecordTerminalSpins _ z.2)).1 =
      observationLeafSpin _ (printedGeneratedMixedCrossOldLeaf U e v hv0 hvJ i) z.2 := by
  unfold printedGeneratedMixedCrossTerminalProjection
  rw [observationRefinementTerminalProject_leaf]
  exact nativeStreamingGeneratedCrossVertexTerminalProjection_old_leaf _ _ _ z.2

private theorem edgeOldSpin {E S : Type}
    (U : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) (i : ObservationLeaf U.tree)
    (z : E × Records E S (nativeStreamingGeneratedCrossEdgeComponent U e f k).tree) :
    observationTerminalSpin U.tree i
      (nativeStreamingGeneratedCrossEdgeTerminalProjection U e f k
        (finiteCascadeRecordTerminalSpins _ z.2)).1 =
      observationLeafSpin _ (printedGeneratedCrossEdgeOldLeaf U e f k i) z.2 := by
  unfold nativeStreamingGeneratedCrossEdgeTerminalProjection
  rw [observationRefinementTerminalProject_leaf]
  exact nativeStreamingGeneratedCrossVertexTerminalProjection_old_leaf _ _ _ z.2

theorem printedGeneratedOriginCrossChart_old_leaf_spin {E S : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart) (i : ObservationLeaf U.tree)
    (z : E × Records E S (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    observationTerminalSpin U.tree i
      (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k
        (finiteCascadeRecordTerminalSpins _ z.2)).1 =
      observationLeafSpin _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k i) z.2 := by
  rcases γ₁ with v | (v | u) <;> rcases γ₂ with w | (w | t)
  · exact nativeStreamingGeneratedCrossVertexTerminalProjection_old_leaf _ _ i z.2
  · exact mixedOldSpin U (printedGeneratedOriginChartEdge U w) (printedGeneratedOriginChartFork U v)
      (printedGeneratedOriginChartFork_interior U v).1
      (printedGeneratedOriginChartFork_interior U v).2 i z
  · change observationTerminalSpin U.tree i
      (nativeStreamingGeneratedEndpointTerminalProject U
        (nativeStreamingGeneratedCrossVertexTerminalProjection _ _
          (finiteCascadeRecordTerminalSpins _ z.2)).1) = _
    rw [nativeStreamingGeneratedEndpointTerminalProject_leaf]
    exact nativeStreamingGeneratedCrossVertexTerminalProjection_old_leaf _ _ _ z.2
  · exact mixedOldSpin U (printedGeneratedOriginChartEdge U v) (printedGeneratedOriginChartFork U w)
      (printedGeneratedOriginChartFork_interior U w).1
      (printedGeneratedOriginChartFork_interior U w).2 i z
  · exact edgeOldSpin U _ _ k i z
  · change observationTerminalSpin U.tree i
      (nativeStreamingGeneratedEndpointTerminalProject U
        (printedGeneratedMixedCrossTerminalProjection (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U v))
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
          (finiteCascadeRecordTerminalSpins
            (nativeStreamingGeneratedMixedCrossComponent (nativeStreamingGeneratedEndpointComponent U)
              (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U v))
              (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
              (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
              (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2).tree z.2)).1) = _
    rw [nativeStreamingGeneratedEndpointTerminalProject_leaf]
    exact mixedOldSpin (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U v))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 _ z
  · change observationTerminalSpin U.tree i
      (nativeStreamingGeneratedEndpointTerminalProject U
        (nativeStreamingGeneratedCrossVertexTerminalProjection _ _
          (finiteCascadeRecordTerminalSpins _ z.2)).1) = _
    rw [nativeStreamingGeneratedEndpointTerminalProject_leaf]
    exact nativeStreamingGeneratedCrossVertexTerminalProjection_old_leaf _ _ _ z.2
  · change observationTerminalSpin U.tree i
      (nativeStreamingGeneratedEndpointTerminalProject U
        (printedGeneratedMixedCrossTerminalProjection (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U w))
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
          (finiteCascadeRecordTerminalSpins
            (nativeStreamingGeneratedMixedCrossComponent (nativeStreamingGeneratedEndpointComponent U)
              (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U w))
              (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
              (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
              (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2).tree z.2)).1) = _
    rw [nativeStreamingGeneratedEndpointTerminalProject_leaf]
    exact mixedOldSpin (nativeStreamingGeneratedEndpointComponent U)
      (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U w))
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 _ z
  · change observationTerminalSpin U.tree i
      (nativeStreamingGeneratedEndpointTerminalProject U
        (nativeStreamingGeneratedCrossVertexTerminalProjection _ _
          (finiteCascadeRecordTerminalSpins _ z.2)).1) = _
    rw [nativeStreamingGeneratedEndpointTerminalProject_leaf]
    exact nativeStreamingGeneratedCrossVertexTerminalProjection_old_leaf _ _ _ z.2

theorem printedGeneratedOriginCrossChart_old_leaf_terminal_spin {S : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart) (i : ObservationLeaf U.tree)
    (σ : TerminalSpins S (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    observationTerminalSpin U.tree i (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ).1 =
      observationTerminalSpin _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k i) σ := by
  have H := printedGeneratedOriginCrossChart_old_leaf_spin U γ₁ γ₂ k i
    ((),observationUnitRecord (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree σ)
  simpa only [←observationTerminalSpin_record, finiteCascadeRecordTerminalSpins_unit] using H

theorem printedGeneratedOriginCrossChart_old_pair_defect {E : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r) (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l)
    (i j : ObservationLeaf U.tree)
    (z : E × Records E (Configuration (n+1))
      (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    cavitySpinOverlapDefect n (nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j))
      (observationTerminalSpin U.tree i
        (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k (finiteCascadeRecordTerminalSpins _ z.2)).1)
      (observationTerminalSpin U.tree j
        (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k (finiteCascadeRecordTerminalSpins _ z.2)).1) =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l)
        (observationCommonLevel _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k i)
          (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k j)))
      (observationLeafSpin _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k i) z.2)
      (observationLeafSpin _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k j) z.2) := by
  rw [printedGeneratedOriginCrossChart_old_pair_clock U γ₁ γ₂ k h r l hh hr hl hk,
    printedGeneratedOriginCrossChart_old_leaf_spin, printedGeneratedOriginCrossChart_old_leaf_spin]

theorem printedGeneratedOriginCrossChart_old_pair_terminal_defect
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r) (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l)
    (i j : ObservationLeaf U.tree)
    (σ : TerminalSpins (Configuration (n+1)) (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    cavitySpinOverlapDefect n (nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i j))
      (observationTerminalSpin U.tree i (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ).1)
      (observationTerminalSpin U.tree j (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ).1) =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l)
        (observationCommonLevel _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k i)
          (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k j)))
      (observationTerminalSpin _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k i) σ)
      (observationTerminalSpin _ (printedGeneratedOriginCrossChartOldLeaf U γ₁ γ₂ k j) σ) := by
  rw [printedGeneratedOriginCrossChart_old_pair_clock U γ₁ γ₂ k h r l hh hr hl hk,
    printedGeneratedOriginCrossChart_old_leaf_terminal_spin, printedGeneratedOriginCrossChart_old_leaf_terminal_spin]

end QuantitativeFollowup
