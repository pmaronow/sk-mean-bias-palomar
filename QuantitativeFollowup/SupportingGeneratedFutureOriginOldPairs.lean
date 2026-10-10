module
public import QuantitativeFollowup.SupportingGeneratedFutureOriginOldPairsGeometry
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiverCheckpoint
public import QuantitativeFollowup.SupportingGeneratedEndpointOldPairs

@[expose] public section

/-! The canonical future chart preserves every original terminal pair and
produces its new defect at two literal fresh leaves.  Active-cell hypotheses
derive the admissible split; inactive finite charts remain total. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def printedGeneratedOriginFutureChartOldLeaf (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth) (i : ObservationLeaf U.tree) :
    ObservationLeaf (printedGeneratedOriginFutureChartComponent U γ j).tree :=
  match γ with
  | .inl k =>
      let v := printedGeneratedOriginChartFork U k
      let hv := printedGeneratedOriginChartFork_interior U k
      printedGeneratedFutureVertexOldLeaf U v hv.1 hv.2 (min j.val (v.depth-1))
        (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos)) i
  | .inr (.inl k) => nativeStreamingGeneratedSharedFutureEdgeOldLeaf U
      (printedGeneratedOriginChartEdge U k) (min j.val (printedGeneratedOriginChartEdge U k).depth)
      (Nat.min_le_right _ _) i
  | .inr (.inr _) =>
      let B := nativeStreamingGeneratedEndpointComponent U
      let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
      let hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
      printedGeneratedFutureVertexOldLeaf B v hv.1 hv.2 (j.val+1)
        (by rw [nativeStreamingGeneratedEndpointVertex_depth]; change j.val+1 < U.depth+1; omega)
        (nativeStreamingGeneratedEndpointLeaf U i)

def printedGeneratedOriginFutureChartFirstLeaf (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth) :
    ObservationLeaf (printedGeneratedOriginFutureChartComponent U γ j).tree :=
  match γ with
  | .inl k =>
      let v := printedGeneratedOriginChartFork U k
      let hv := printedGeneratedOriginChartFork_interior U k
      printedGeneratedFutureVertexFirstLeaf U v hv.1 hv.2 (min j.val (v.depth-1))
        (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos))
  | .inr (.inl k) => nativeStreamingGeneratedSharedFutureEdgeFirstLeaf U
      (printedGeneratedOriginChartEdge U k) (min j.val (printedGeneratedOriginChartEdge U k).depth)
      (Nat.min_le_right _ _)
  | .inr (.inr _) =>
      let B := nativeStreamingGeneratedEndpointComponent U
      let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
      let hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
      printedGeneratedFutureVertexFirstLeaf B v hv.1 hv.2 (j.val+1)
        (by rw [nativeStreamingGeneratedEndpointVertex_depth]; change j.val+1 < U.depth+1; omega)

def printedGeneratedOriginFutureChartSecondLeaf (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth) :
    ObservationLeaf (printedGeneratedOriginFutureChartComponent U γ j).tree :=
  match γ with
  | .inl k =>
      let v := printedGeneratedOriginChartFork U k
      let hv := printedGeneratedOriginChartFork_interior U k
      printedGeneratedFutureVertexSecondLeaf U v hv.1 hv.2 (min j.val (v.depth-1))
        (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos))
  | .inr (.inl k) => nativeStreamingGeneratedSharedFutureEdgeSecondLeaf U
      (printedGeneratedOriginChartEdge U k) (min j.val (printedGeneratedOriginChartEdge U k).depth)
      (Nat.min_le_right _ _)
  | .inr (.inr _) =>
      let B := nativeStreamingGeneratedEndpointComponent U
      let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
      let hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
      printedGeneratedFutureVertexSecondLeaf B v hv.1 hv.2 (j.val+1)
        (by rw [nativeStreamingGeneratedEndpointVertex_depth]; change j.val+1 < U.depth+1; omega)

theorem printedGeneratedFutureEdgeTerminalProject_old_leaf
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (j : ℕ) (hj : j ≤ e.depth) (i : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n (nativeStreamingGeneratedSharedFutureEdgeComponent U e j hj)) :
    observationTerminalSpin U.tree i (printedGeneratedFutureEdgeTerminalProject U e j hj σ).1 =
      observationTerminalSpin _ (nativeStreamingGeneratedSharedFutureEdgeOldLeaf U e j hj i) σ :=
  printedGeneratedRefinedFutureTerminalProject_old_leaf _ _ _ _ i σ

theorem printedGeneratedFutureEdgeTerminalProject_pair
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (j : ℕ) (hj : j ≤ e.depth)
    (σ : CavityGeneratedComponentTerminal n (nativeStreamingGeneratedSharedFutureEdgeComponent U e j hj)) :
    (printedGeneratedFutureEdgeTerminalProject U e j hj σ).2 =
      (observationTerminalSpin _ (nativeStreamingGeneratedSharedFutureEdgeFirstLeaf U e j hj) σ,
        observationTerminalSpin _ (nativeStreamingGeneratedSharedFutureEdgeSecondLeaf U e j hj) σ) :=
  printedGeneratedRefinedFutureTerminalProject_pair _ _ _ _ σ

theorem printedGeneratedFutureEdgeOldLeaves_commonClock
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (j : ℕ) (hj : j ≤ e.depth) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth)
    (hl : nativeStreamingGeneratedComponentClock U h (j+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j) (hrl : r < l)
    (i k : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeComponent U e j hj)
      (nativeStreamingGeneratedCrossEdgeAppend h r l)
      (observationCommonLevel _ (nativeStreamingGeneratedSharedFutureEdgeOldLeaf U e j hj i)
        (nativeStreamingGeneratedSharedFutureEdgeOldLeaf U e j hj k)) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i k) := by
  rw [nativeStreamingGeneratedSharedFutureEdgeComponent_clock,
    nativeStreamingGeneratedSharedFutureEdgeObserved_clock_append U e j hj h r l hh hr hl hrl]
  change nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock U h) e.depth j r l
    (observationCommonLevel _
      (finiteCascadeContinuationOldLeaf _ (nativeStreamingGeneratedSharedFutureEdgeAnchor U e j hj)
        (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree i))
      (finiteCascadeContinuationOldLeaf _ (nativeStreamingGeneratedSharedFutureEdgeAnchor U e j hj)
        (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree k))) = _
  rw [finiteCascadeContinuationOldLeaf_commonLevel]
  change nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock U h) e.depth j r l
    (observationCommonLevel (observationRefineTree nativeStreamingPairObservationSubdivision U.tree)
      (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree i)
      (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision U.tree k)) = _
  rw [observationRefinementLeafEmbed_commonLevel,nativeStreamingPairObservationSchedule_refinement]

theorem printedGeneratedOriginFutureChartTerminalProject_old_leaf
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (j : Fin U.depth) (i : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent U γ j)) :
    observationTerminalSpin U.tree i (printedGeneratedFutureOriginChartTerminalProject U γ j σ).1 =
      observationTerminalSpin _ (printedGeneratedOriginFutureChartOldLeaf U γ j i) σ := by
  rcases γ with k | (k | u)
  · let v := printedGeneratedOriginChartFork U k
    have hv := printedGeneratedOriginChartFork_interior U k
    have hd : min j.val (v.depth-1) < v.depth :=
      Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos)
    exact printedGeneratedFutureVertexTerminalProject_old_leaf U v hv.1 hv.2 _ hd i σ
  · exact printedGeneratedFutureEdgeTerminalProject_old_leaf U _ _ _ i σ
  · change observationTerminalSpin U.tree i
      (nativeStreamingGeneratedEndpointTerminalProject U
        (printedGeneratedFutureVertexTerminalProject (nativeStreamingGeneratedEndpointComponent U)
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree)) _ _ (j.val+1) _ σ).1) = _
    rw [nativeStreamingGeneratedEndpointTerminalProject_leaf]
    exact printedGeneratedFutureVertexTerminalProject_old_leaf _ _ _ _ _ _ _ σ

theorem printedGeneratedOriginFutureChartTerminalProject_pair
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (j : Fin U.depth)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent U γ j)) :
    (printedGeneratedFutureOriginChartTerminalProject U γ j σ).2 =
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartFirstLeaf U γ j) σ,
        observationTerminalSpin _ (printedGeneratedOriginFutureChartSecondLeaf U γ j) σ) := by
  rcases γ with k | (k | u)
  · let v := printedGeneratedOriginChartFork U k
    have hv := printedGeneratedOriginChartFork_interior U k
    have hd : min j.val (v.depth-1) < v.depth :=
      Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos)
    exact printedGeneratedFutureVertexTerminalProject_pair U v hv.1 hv.2 _ hd σ
  · exact printedGeneratedFutureEdgeTerminalProject_pair U _ _ _ σ
  · let B := nativeStreamingGeneratedEndpointComponent U
    let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
    have hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
    have hd : j.val+1 < v.depth := by
      rw [nativeStreamingGeneratedEndpointVertex_depth]
      change j.val+1 < U.depth+1
      omega
    exact printedGeneratedFutureVertexTerminalProject_pair B v hv.1 hv.2 _ hd σ

theorem printedGeneratedOriginFutureChartFirstLeaf_ne_second
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (j : Fin U.depth) :
    printedGeneratedOriginFutureChartFirstLeaf U γ j ≠
      printedGeneratedOriginFutureChartSecondLeaf U γ j := by
  rcases γ with k | (k | u)
  · exact printedGeneratedRefinedFutureFirstLeaf_ne_second _ _ _ _
  · exact nativeStreamingGeneratedSharedFutureEdgeFirstLeaf_ne_second U _ _ _
  · exact printedGeneratedRefinedFutureFirstLeaf_ne_second _ _ _ _

private theorem futureOldPairs_fork_index
    (U : CavityGeneratedConstructedComponent m)
    (i : Fin (cavityGeneratedOriginForkVertices U.tree).length) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (l : Paper.Overlap)
    (hl : l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hf : nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartFork U i).depth < l) :
    j.val < (printedGeneratedOriginChartFork U i).depth := by
  by_contra hn
  exact (not_lt_of_ge (hl.trans (nativeStreamingGeneratedComponentClock_antitone U h
    (show (printedGeneratedOriginChartFork U i).depth ≤ j.val by omega)))) hf

private theorem futureOldPairs_edge_index
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r)
    (hl : l ≤ nativeStreamingGeneratedComponentClock U h j) (hf : r < l) : j.val ≤ e.depth := by
  by_contra hn
  exact (not_lt_of_ge (hl.trans ((nativeStreamingGeneratedComponentClock_antitone U h
    (show e.depth+1 ≤ j.val by omega)).trans hr))) hf

theorem printedGeneratedOriginFutureChartOldLeaves_commonClock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hf : printedGeneratedOriginChartClock U γ h r < l) (i k : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent U γ j)
      (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l)
      (observationCommonLevel _ (printedGeneratedOriginFutureChartOldLeaf U γ j i)
        (printedGeneratedOriginFutureChartOldLeaf U γ j k)) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i k) := by
  rcases γ with t | (t | u)
  · let v := printedGeneratedOriginChartFork U t
    have hv := printedGeneratedOriginChartFork_interior U t
    have hj : j.val < v.depth := futureOldPairs_fork_index U t j h l hl.2 hf
    have hmin : min j.val (v.depth-1) = j.val := Nat.min_eq_left (by omega)
    have hd : min j.val (v.depth-1) < v.depth :=
      Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos)
    have hlp : nativeStreamingGeneratedComponentClock U h (min j.val (v.depth-1)+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock U h (min j.val (v.depth-1)) := by
      simpa only [hmin] using hl
    exact printedGeneratedFutureVertexOldLeaves_commonClock U v hv.1 hv.2 _ hd h l hh hlp i k
  · let e := printedGeneratedOriginChartEdge U t
    have hj := futureOldPairs_edge_index U e j h r l hr.1 hl.2 hf
    have hmin : min j.val e.depth = j.val := Nat.min_eq_left hj
    have hlp : nativeStreamingGeneratedComponentClock U h (min j.val e.depth+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock U h (min j.val e.depth) := by
      simpa only [hmin] using hl
    exact printedGeneratedFutureEdgeOldLeaves_commonClock U e _ (Nat.min_le_right _ _) h r l hh hr hlp hf i k
  · let B := nativeStreamingGeneratedEndpointComponent U
    let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
    have hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
    have hj : j.val+1 < v.depth := by
      rw [nativeStreamingGeneratedEndpointVertex_depth]
      change j.val+1 < U.depth+1
      omega
    have hB : h ∈ nativeStreamingGeneratedComponentOrderSet B := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have hlB : nativeStreamingGeneratedComponentClock B h (j.val+1+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock B h (j.val+1) := by
      change nativeStreamingGeneratedEndpointClock U h (j.val+1+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedEndpointClock U h (j.val+1)
      simpa only [nativeStreamingGeneratedEndpointClock_succ] using hl
    have he := printedGeneratedFutureVertexOldLeaves_commonClock B v hv.1 hv.2 _ hj h l hB hlB
      (nativeStreamingGeneratedEndpointLeaf U i) (nativeStreamingGeneratedEndpointLeaf U k)
    rw [nativeStreamingGeneratedEndpointVertex_clock] at he
    exact he.trans (nativeStreamingGeneratedEndpointOldLeaves_commonClock U h i k)

theorem printedGeneratedOriginFutureChartFreshLeaves_commonClock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hf : printedGeneratedOriginChartClock U γ h r < l) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent U γ j)
      (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l)
      (observationCommonLevel _ (printedGeneratedOriginFutureChartFirstLeaf U γ j)
        (printedGeneratedOriginFutureChartSecondLeaf U γ j)) = l := by
  rcases γ with t | (t | u)
  · let v := printedGeneratedOriginChartFork U t
    have hv := printedGeneratedOriginChartFork_interior U t
    have hj : j.val < v.depth := futureOldPairs_fork_index U t j h l hl.2 hf
    have hmin : min j.val (v.depth-1) = j.val := Nat.min_eq_left (by omega)
    have hd : min j.val (v.depth-1) < v.depth :=
      Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos)
    have hlp : nativeStreamingGeneratedComponentClock U h (min j.val (v.depth-1)+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock U h (min j.val (v.depth-1)) := by
      simpa only [hmin] using hl
    exact printedGeneratedFutureVertexFreshLeaves_commonClock U v hv.1 hv.2 _ hd h l hh hlp
  · let e := printedGeneratedOriginChartEdge U t
    have hj := futureOldPairs_edge_index U e j h r l hr.1 hl.2 hf
    have hmin : min j.val e.depth = j.val := Nat.min_eq_left hj
    have hlp : nativeStreamingGeneratedComponentClock U h (min j.val e.depth+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock U h (min j.val e.depth) := by
      simpa only [hmin] using hl
    exact nativeStreamingGeneratedSharedFutureEdgeLeaves_commonClock U e _ (Nat.min_le_right _ _)
      h r l hh hr hlp hf
  · let B := nativeStreamingGeneratedEndpointComponent U
    let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
    have hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
    have hj : j.val+1 < v.depth := by
      rw [nativeStreamingGeneratedEndpointVertex_depth]
      change j.val+1 < U.depth+1
      omega
    have hB : h ∈ nativeStreamingGeneratedComponentOrderSet B := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have hlB : nativeStreamingGeneratedComponentClock B h (j.val+1+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock B h (j.val+1) := by
      change nativeStreamingGeneratedEndpointClock U h (j.val+1+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedEndpointClock U h (j.val+1)
      simpa only [nativeStreamingGeneratedEndpointClock_succ] using hl
    have he := printedGeneratedFutureVertexFreshLeaves_commonClock B v hv.1 hv.2 _ hj h l hB hlB
    rw [nativeStreamingGeneratedEndpointVertex_clock] at he
    exact he

theorem printedGeneratedOriginFutureChartOldPair_defect
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j) (hf : printedGeneratedOriginChartClock U γ h r < l)
    (i k : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent U γ j)) :
    cavitySpinOverlapDefect n (nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i k))
      (observationTerminalSpin U.tree i (printedGeneratedFutureOriginChartTerminalProject U γ j σ).1)
      (observationTerminalSpin U.tree k (printedGeneratedFutureOriginChartTerminalProject U γ j σ).1) =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent U γ j)
        (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l)
        (observationCommonLevel _ (printedGeneratedOriginFutureChartOldLeaf U γ j i)
          (printedGeneratedOriginFutureChartOldLeaf U γ j k)))
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartOldLeaf U γ j i) σ)
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartOldLeaf U γ j k) σ) := by
  rw [printedGeneratedOriginFutureChartOldLeaves_commonClock U γ j h r l hh hr hl hf,
    printedGeneratedOriginFutureChartTerminalProject_old_leaf,
    printedGeneratedOriginFutureChartTerminalProject_old_leaf]

theorem printedGeneratedOriginFutureChartFreshPair_defect
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j) (hf : printedGeneratedOriginChartClock U γ h r < l)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent U γ j)) :
    cavitySpinOverlapDefect n l (printedGeneratedFutureOriginChartTerminalProject U γ j σ).2.1
      (printedGeneratedFutureOriginChartTerminalProject U γ j σ).2.2 =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent U γ j)
        (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l)
        (observationCommonLevel _ (printedGeneratedOriginFutureChartFirstLeaf U γ j)
          (printedGeneratedOriginFutureChartSecondLeaf U γ j)))
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartFirstLeaf U γ j) σ)
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartSecondLeaf U γ j) σ) := by
  rw [printedGeneratedOriginFutureChartFreshLeaves_commonClock U γ j h r l hh hr hl hf,
    printedGeneratedOriginFutureChartTerminalProject_pair]

private theorem futureOldPairs_component_order
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h ∈ W.clockTemplate.orderSet) :
    h ∈ nativeStreamingGeneratedComponentOrderSet (W.component c) := by
  intro j
  have he (p : ℕ) :
      (cavityGeneratedFiniteClockLabels (W.component c).label p).value h =
        W.clockTemplate.rawClock h c p := by
    by_cases hp : p ≤ W.depth c
    · simp only [cavityGeneratedFiniteClockLabels,CavityGeneratedConstructedForest.component,
        CavityGeneratedConstructedForest.clockTemplate,CavityGeneratedForestClockTemplate.rawClock,dif_pos hp]
    · simp only [cavityGeneratedFiniteClockLabels,CavityGeneratedConstructedForest.component,
        CavityGeneratedConstructedForest.clockTemplate,CavityGeneratedForestClockTemplate.rawClock,
        dif_neg hp,CavityGeneratedClockLabel.value]
  simpa only [he] using hh c j

private theorem futureOldPairs_source_append
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j) :
    cavityGeneratedFutureOriginChartAppend W c z = nativeStreamingGeneratedCrossEdgeAppend z.1.1
      (printedGeneratedOriginChartClock (W.component c) γ z.1.1
        (printedGeneratedFuturePayloadFreeClock (W.component c) z.1.2)) z.2 := by
  have hγ : printedGeneratedFuturePayloadChart (W.component c) z.1.2 = γ := hz.1.1
  unfold cavityGeneratedFutureOriginChartAppend
  rw [printedGeneratedFutureSelectionClock_eq_chart,hγ]

theorem cavityGeneratedFutureOriginSource_oldLeaves_commonClock
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j) (i k : ObservationLeaf (W.tree c)) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent (W.component c) γ j)
      (cavityGeneratedFutureOriginChartAppend W c z)
      (observationCommonLevel _ (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j i)
        (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j k)) =
      nativeStreamingGeneratedComponentClock (W.component c) z.1.1 (observationCommonLevel (W.tree c) i k) := by
  rw [futureOldPairs_source_append W c γ j z hz]
  have hγ : printedGeneratedFuturePayloadChart (W.component c) z.1.2 = γ := hz.1.1
  have ht := printedGeneratedFutureSelectionClock_eq_chart W c z.1
  rw [hγ] at ht
  exact printedGeneratedOriginFutureChartOldLeaves_commonClock (W.component c) γ j z.1.1
    (printedGeneratedFuturePayloadFreeClock (W.component c) z.1.2) z.2
    (futureOldPairs_component_order W c z.1.1 hz.1.2.1) hz.1.2.2.1 hz.1.2.2.2.1
    (by simpa only [ht] using hz.1.2.2.2.2) i k

theorem cavityGeneratedFutureOriginSource_freshLeaves_commonClock
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent (W.component c) γ j)
      (cavityGeneratedFutureOriginChartAppend W c z)
      (observationCommonLevel _ (printedGeneratedOriginFutureChartFirstLeaf (W.component c) γ j)
        (printedGeneratedOriginFutureChartSecondLeaf (W.component c) γ j)) = z.2 := by
  rw [futureOldPairs_source_append W c γ j z hz]
  have hγ : printedGeneratedFuturePayloadChart (W.component c) z.1.2 = γ := hz.1.1
  have ht := printedGeneratedFutureSelectionClock_eq_chart W c z.1
  rw [hγ] at ht
  exact printedGeneratedOriginFutureChartFreshLeaves_commonClock (W.component c) γ j z.1.1
    (printedGeneratedFuturePayloadFreeClock (W.component c) z.1.2) z.2
    (futureOldPairs_component_order W c z.1.1 hz.1.2.1) hz.1.2.2.1 hz.1.2.2.2.1
    (by simpa only [ht] using hz.1.2.2.2.2)

theorem cavityGeneratedFutureOriginSource_oldPair_defect
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j) (i k : ObservationLeaf (W.tree c))
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent (W.component c) γ j)) :
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (W.component c) z.1.1 (observationCommonLevel (W.tree c) i k))
      (observationTerminalSpin (W.tree c) i (printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j σ).1)
      (observationTerminalSpin (W.tree c) k (printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j σ).1) =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent (W.component c) γ j)
        (cavityGeneratedFutureOriginChartAppend W c z)
        (observationCommonLevel _ (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j i)
          (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j k)))
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j i) σ)
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j k) σ) := by
  rw [cavityGeneratedFutureOriginSource_oldLeaves_commonClock W c γ j z hz i k]
  exact congrArg₂ (cavitySpinOverlapDefect n
    (nativeStreamingGeneratedComponentClock (W.component c) z.1.1 (observationCommonLevel (W.tree c) i k)))
    (printedGeneratedOriginFutureChartTerminalProject_old_leaf (W.component c) γ j i σ)
    (printedGeneratedOriginFutureChartTerminalProject_old_leaf (W.component c) γ j k σ)

theorem cavityGeneratedFutureOriginSource_freshPair_defect
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent (W.component c) γ j)) :
    cavitySpinOverlapDefect n z.2 (printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j σ).2.1
      (printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j σ).2.2 =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent (W.component c) γ j)
        (cavityGeneratedFutureOriginChartAppend W c z)
        (observationCommonLevel _ (printedGeneratedOriginFutureChartFirstLeaf (W.component c) γ j)
          (printedGeneratedOriginFutureChartSecondLeaf (W.component c) γ j)))
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartFirstLeaf (W.component c) γ j) σ)
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartSecondLeaf (W.component c) γ j) σ) := by
  rw [cavityGeneratedFutureOriginSource_freshLeaves_commonClock W c γ j z hz,
    printedGeneratedOriginFutureChartTerminalProject_pair]

def cavityGeneratedFutureOriginChosenTerminal
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent (W.component c) γ j) :=
  (cavityGeneratedForestReplacementSelectedEquiv (n:=n)
    (W.reindex (fun i => i.castSucc.castSucc)) c
    (printedGeneratedOriginFutureChartComponent (W.component c) γ j)).symm (σ c)

theorem cavityGeneratedFutureOriginSelectedProjection_pair
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    (cavityGeneratedFutureOriginSelectedProjection W c γ j σ).2 =
      (observationTerminalSpin _ (printedGeneratedOriginFutureChartFirstLeaf (W.component c) γ j)
        (cavityGeneratedFutureOriginChosenTerminal W c γ j σ),
        observationTerminalSpin _ (printedGeneratedOriginFutureChartSecondLeaf (W.component c) γ j)
          (cavityGeneratedFutureOriginChosenTerminal W c γ j σ)) :=
  printedGeneratedOriginFutureChartTerminalProject_pair _ _ _ _

theorem cavityGeneratedFutureOriginOldTerminal_selected_leaf
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (i : ObservationLeaf (W.tree c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    observationTerminalSpin (W.tree c) i (cavityGeneratedFutureOriginOldTerminal W c γ j σ c) =
      observationTerminalSpin _ (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j i)
        (cavityGeneratedFutureOriginChosenTerminal W c γ j σ) := by
  simp only [cavityGeneratedFutureOriginOldTerminal,dif_pos rfl,cast_eq]
  exact printedGeneratedOriginFutureChartTerminalProject_old_leaf (W.component c) γ j i
    (cavityGeneratedFutureOriginChosenTerminal W c γ j σ)

theorem cavityGeneratedFutureOriginTest_source_pair
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    cavityGeneratedFutureOriginTest W c γ j F (cavityGeneratedFutureOriginChartAppend W c z) σ =
    F (z.1.1,cavityGeneratedFutureOriginOldTerminal W c γ j σ) *
      cavitySpinOverlapDefect n
        (nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent (W.component c) γ j)
          (cavityGeneratedFutureOriginChartAppend W c z)
          (observationCommonLevel _ (printedGeneratedOriginFutureChartFirstLeaf (W.component c) γ j)
            (printedGeneratedOriginFutureChartSecondLeaf (W.component c) γ j)))
        (observationTerminalSpin _ (printedGeneratedOriginFutureChartFirstLeaf (W.component c) γ j)
          (cavityGeneratedFutureOriginChosenTerminal W c γ j σ))
        (observationTerminalSpin _ (printedGeneratedOriginFutureChartSecondLeaf (W.component c) γ j)
          (cavityGeneratedFutureOriginChosenTerminal W c γ j σ)) := by
  rw [cavityGeneratedFutureOriginSource_freshLeaves_commonClock W c γ j z hz]
  simp only [cavityGeneratedFutureOriginTest,cavityGeneratedFutureOriginTerminalProjection,
    cavityGeneratedFutureOriginChartAppend,nativeStreamingGeneratedCrossEdgeAppend,
    cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last,cavityGeneratedFutureOriginSelectedProjection_pair]

end QuantitativeFollowup
