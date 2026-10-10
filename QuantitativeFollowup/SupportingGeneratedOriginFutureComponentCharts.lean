module
public import QuantitativeFollowup.SupportingGeneratedOriginComponentCharts
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFuturePatternsCheckpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFutureEdgePatternsCheckpoint

@[expose] public section

/-! Actual future outputs for selected original fork, edge, and root charts.
Inactive finite charts have genuine clamped outputs; the actual strict-future
cell derives the original, unclamped index. Each output has exactly two new
leaves. The first appended mark is the selected original clock. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m J : ℕ}

theorem generatedFuture_exists_edge_depth (T : FiniteTerminalGenealogy J)
    (j : ℕ) (hj : j < J) : ∃e : NativeStreamingEdge T, e.depth = j := by
  induction T generalizing j with
  | leaf => omega
  | @advance d T ih =>
      by_cases he : j = d
      · exact ⟨.here T, he.symm⟩
      · obtain ⟨e,he⟩ := ih j (by omega)
        exact ⟨.child e,he⟩
  | fork T V ihT ihV =>
      obtain ⟨e,he⟩ := ihT j hj
      exact ⟨.left e,he⟩

def printedGeneratedFutureCellEdge (U : CavityGeneratedConstructedComponent m)
    (j : ℕ) (hj : j < U.depth) : NativeStreamingEdge U.tree :=
  Classical.choose (generatedFuture_exists_edge_depth U.tree j hj)

theorem printedGeneratedFutureCellEdge_depth (U : CavityGeneratedConstructedComponent m)
    (j : ℕ) (hj : j < U.depth) : (printedGeneratedFutureCellEdge U j hj).depth = j :=
  Classical.choose_spec (generatedFuture_exists_edge_depth U.tree j hj)

/-- Copy the selected origin into the new mark without adding a terminal leaf. -/
def printedGeneratedFutureVertexBase (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) :
    CavityGeneratedConstructedComponent (m+1) where
  depth := U.depth
  tree := U.tree
  label := nativeStreamingGeneratedVertexLabels U v.depth
  terminal_label := by
    unfold nativeStreamingGeneratedVertexLabels
    rw [if_neg (by change ¬0=v.depth; omega),U.terminal_label]
    rfl
  initial_label := by
    unfold nativeStreamingGeneratedVertexLabels
    rw [if_neg (by change U.depth≠v.depth; omega),U.initial_label]
    rfl
  construction := by
    rw [nativeStreamingGeneratedVertexLabels_global U v.depth hvJ.le]
    exact U.construction.attached_clock_relabel v.depth

theorem printedGeneratedFutureVertexBase_label (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) :
    cavityGeneratedFiniteClockLabels (printedGeneratedFutureVertexBase U v hv0 hvJ).label v.depth =
      .mark (Fin.last m) := by
  change cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedVertexLabels U v.depth) v.depth = _
  rw [nativeStreamingGeneratedVertexLabels_global U v.depth hvJ.le]
  exact cavityGeneratedAttachedClockLabels_at_depth _ _

theorem printedGeneratedFutureVertexBase_snoc_raw (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) (j : ℕ) :
    (cavityGeneratedFiniteClockLabels (printedGeneratedFutureVertexBase U v hv0 hvJ).label j).value
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)) =
        nativeStreamingGeneratedComponentClock U h j :=
  printedGeneratedVertexComponent_snoc_raw U v hv0 hvJ .single h hh j

theorem printedGeneratedFutureVertexBase_snoc_order (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth) ∈
      nativeStreamingGeneratedComponentOrderSet (printedGeneratedFutureVertexBase U v hv0 hvJ) :=
  printedGeneratedVertexComponent_snoc_order U v hv0 hvJ .single h hh

theorem printedGeneratedFutureVertexBase_clock_snoc (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    nativeStreamingGeneratedComponentClock (printedGeneratedFutureVertexBase U v hv0 hvJ)
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)) =
      nativeStreamingGeneratedComponentClock U h := by
  funext j
  rw [←nativeStreamingGeneratedComponent_raw_eq_clock_of_order _ _
    (printedGeneratedFutureVertexBase_snoc_order U v hv0 hvJ h hh)]
  exact printedGeneratedFutureVertexBase_snoc_raw U v hv0 hvJ h hh j

def printedGeneratedFutureVertexComponent (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (j : ℕ) (hj : j < v.depth) : CavityGeneratedConstructedComponent (m+2) :=
  nativeStreamingGeneratedSharedFutureComponent (printedGeneratedFutureVertexBase U v hv0 hvJ)
    v (Fin.last m) (printedGeneratedFutureVertexBase_label U v hv0 hvJ)
    (printedGeneratedFutureCellEdge (printedGeneratedFutureVertexBase U v hv0 hvJ) j (hj.trans hvJ))
    (by rw [printedGeneratedFutureCellEdge_depth]; exact hj)

private theorem generatedFuture_vertex_component_raw
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) (p : ℕ) :
    (cavityGeneratedFiniteClockLabels (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj).label p).value
      (nativeStreamingGeneratedCrossEdgeAppend h (nativeStreamingGeneratedComponentClock U h v.depth) l) =
      nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h) j l p := by
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels B e) p).value _ = _
  rw [nativeStreamingGeneratedEdgeLabels_global]
  simp only [nativeStreamingGeneratedCrossEdgeAppend]
  rw [nativeStreamingGeneratedEdgeGlobalLabels_snoc_value]
  have he : e.depth = j := printedGeneratedFutureCellEdge_depth B j (hj.trans hvJ)
  rw [he]
  congr 1
  funext d
  exact printedGeneratedFutureVertexBase_snoc_raw U v hv0 hvJ h hh d

theorem printedGeneratedFutureVertexComponent_leafCount
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth) :
    cavityGeneratedComponentLeafCount (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj) =
      cavityGeneratedComponentLeafCount U + 2 := by
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  change FiniteCascadeGenealogy.leafCount (asGenealogy
    (finiteCascadeFutureVertexGraft (nativeStreamingGeneratedSharedFutureAnchor B v e) (e.depth+1))) = _
  rw [finiteCascadeFutureVertexGraft_leafCount]
  change FiniteCascadeGenealogy.leafCount (asGenealogy
    (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) B.tree)) + 2 = _
  rw [leafCount_observationRefineTree]
  rfl

private theorem generatedFuture_edge_component_raw
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (j : ℕ) (hj : j ≤ e.depth) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hrl : r < l) (p : ℕ) :
    (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedSharedFutureEdgeComponent U e j hj).label p).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l) =
      nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock U h) e.depth j r l p := by
  change (cavityGeneratedFiniteClockLabels
    (nativeStreamingGeneratedPairObservationLabels U e.depth j e.depth_lt (hj.trans_lt e.depth_lt)
      (nativeStreamingGeneratedSharedFutureEdgeChart e.depth j)) p).value _ = _
  rw [nativeStreamingGeneratedPairObservationLabels_global,
    nativeStreamingGeneratedPairObservationGlobalLabels_append U e.depth j e.depth_lt
      (hj.trans_lt e.depth_lt) _ h r l (nativeStreamingGeneratedSharedFutureEdgeChart_holds _ _ _ _ hrl)]
  congr 1
  funext d
  exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh d

/-- Total finite output chart; clamping affects only inactive source cells. -/
def printedGeneratedOriginFutureChartComponent (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth) : CavityGeneratedConstructedComponent (m+2) :=
  match γ with
  | .inl i =>
      let v := printedGeneratedOriginChartFork U i
      let hv := printedGeneratedOriginChartFork_interior U i
      printedGeneratedFutureVertexComponent U v hv.1 hv.2 (min j.val (v.depth-1))
        (Nat.lt_of_le_of_lt (Nat.min_le_right j.val (v.depth-1)) (Nat.sub_lt hv.1 Nat.one_pos))
  | .inr (.inl i) =>
      let e := printedGeneratedOriginChartEdge U i
      nativeStreamingGeneratedSharedFutureEdgeComponent U e (min j.val e.depth) (Nat.min_le_right _ _)
  | .inr (.inr _) =>
      let B := nativeStreamingGeneratedEndpointComponent U
      let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
      let hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
      printedGeneratedFutureVertexComponent B v hv.1 hv.2 (j.val+1)
        (by rw [nativeStreamingGeneratedEndpointVertex_depth]; change j.val+1 < U.depth+1; omega)

def printedGeneratedOriginFutureChartSchedule (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap) : ℕ → Paper.Overlap :=
  match γ with
  | .inl _ => nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h) j l
  | .inr (.inl i) => nativeStreamingPairObservationSchedule
      (nativeStreamingGeneratedComponentClock U h) (printedGeneratedOriginChartEdge U i).depth j r l
  | .inr (.inr _) => nativeStreamingEdgeSchedule (nativeStreamingGeneratedEndpointClock U h) (j.val+1) l

private theorem generatedFuture_fork_active_index
    (U : CavityGeneratedConstructedComponent m)
    (i : Fin (cavityGeneratedOriginForkVertices U.tree).length) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (l : Paper.Overlap)
    (hl : l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hfuture : nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartFork U i).depth < l) :
    j.val < (printedGeneratedOriginChartFork U i).depth := by
  by_contra hn
  have hq := nativeStreamingGeneratedComponentClock_antitone U h (show (printedGeneratedOriginChartFork U i).depth ≤ j.val by omega)
  exact (not_lt_of_ge (hl.trans hq)) hfuture

private theorem generatedFuture_edge_active_index
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r)
    (hl : l ≤ nativeStreamingGeneratedComponentClock U h j) (hfuture : r < l) : j.val ≤ e.depth := by
  by_contra hn
  have hq := nativeStreamingGeneratedComponentClock_antitone U h (show e.depth+1 ≤ j.val by omega)
  exact (not_lt_of_ge (hl.trans (hq.trans hr))) hfuture

theorem printedGeneratedOriginFutureChartComponent_append_raw
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧ l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hfuture : printedGeneratedOriginChartClock U γ h r < l) (p : ℕ) :
    (cavityGeneratedFiniteClockLabels (printedGeneratedOriginFutureChartComponent U γ j).label p).value
      (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l) =
      printedGeneratedOriginFutureChartSchedule U γ j h r l p := by
  rcases γ with i | (i | u)
  · have hj := generatedFuture_fork_active_index U i j h l hl.2 hfuture
    have hmin : min j.val ((printedGeneratedOriginChartFork U i).depth-1) = j.val :=
      Nat.min_eq_left (by omega)
    let v := printedGeneratedOriginChartFork U i
    have hv := printedGeneratedOriginChartFork_interior U i
    have hd : min j.val (v.depth-1) < v.depth := by
      exact Nat.lt_of_le_of_lt (Nat.min_le_right j.val (v.depth-1)) (Nat.sub_lt hv.1 Nat.one_pos)
    have he := generatedFuture_vertex_component_raw U v hv.1 hv.2
      (min j.val (v.depth-1)) hd h l hh p
    exact he.trans (congrArg (fun d => nativeStreamingEdgeSchedule
      (nativeStreamingGeneratedComponentClock U h) d l p) hmin)
  · have hj := generatedFuture_edge_active_index U (printedGeneratedOriginChartEdge U i) j h r l hr.1 hl.2 hfuture
    have hmin : min j.val (printedGeneratedOriginChartEdge U i).depth = j.val := Nat.min_eq_left hj
    have he := generatedFuture_edge_component_raw U (printedGeneratedOriginChartEdge U i)
      (min j.val (printedGeneratedOriginChartEdge U i).depth) (Nat.min_le_right _ _)
      h r l hh hfuture p
    exact he.trans (congrArg (fun d => nativeStreamingPairObservationSchedule
      (nativeStreamingGeneratedComponentClock U h) (printedGeneratedOriginChartEdge U i).depth d r l p) hmin)
  · have hhp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have he := generatedFuture_vertex_component_raw (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 (j.val+1)
      (by rw [nativeStreamingGeneratedEndpointVertex_depth]; change j.val+1 < U.depth+1; omega)
      h l hhp p
    rw [nativeStreamingGeneratedEndpointVertex_clock,nativeStreamingGeneratedEndpointComponent_clock] at he
    exact he

theorem printedGeneratedOriginFutureChartSchedule_antitone
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧ l ≤ nativeStreamingGeneratedComponentClock U h j) :
    Antitone (printedGeneratedOriginFutureChartSchedule U γ j h r l) := by
  rcases γ with i | (i | u)
  · exact nativeStreamingEdgeSchedule_antitone _ (nativeStreamingGeneratedComponentClock_antitone U h) j l hl
  · exact nativeStreamingPairObservationSchedule_antitone _ (nativeStreamingGeneratedComponentClock_antitone U h)
      (printedGeneratedOriginChartEdge U i).depth j r l hr hl
  · apply nativeStreamingEdgeSchedule_antitone _
      (nativeStreamingGeneratedComponentClock_antitone (nativeStreamingGeneratedEndpointComponent U) h) (j.val+1) l
    simpa only [nativeStreamingGeneratedEndpointComponent_clock,nativeStreamingGeneratedEndpointClock_succ] using hl

theorem printedGeneratedOriginFutureChartComponent_append_order
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧ l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hfuture : printedGeneratedOriginChartClock U γ h r < l) :
    nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l ∈
      nativeStreamingGeneratedComponentOrderSet (printedGeneratedOriginFutureChartComponent U γ j) := by
  intro p
  rw [printedGeneratedOriginFutureChartComponent_append_raw U γ j h r l hh hr hl hfuture,
    printedGeneratedOriginFutureChartComponent_append_raw U γ j h r l hh hr hl hfuture]
  exact printedGeneratedOriginFutureChartSchedule_antitone U γ j h r l hr hl (Nat.le_succ p.val)

theorem printedGeneratedOriginFutureChartComponent_clock_append
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧ l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hfuture : printedGeneratedOriginChartClock U γ h r < l) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginFutureChartComponent U γ j)
      (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l) =
      printedGeneratedOriginFutureChartSchedule U γ j h r l := by
  funext p
  rw [←nativeStreamingGeneratedComponent_raw_eq_clock_of_order _ _
    (printedGeneratedOriginFutureChartComponent_append_order U γ j h r l hh hr hl hfuture)]
  exact printedGeneratedOriginFutureChartComponent_append_raw U γ j h r l hh hr hl hfuture p

theorem printedGeneratedOriginFutureChartComponent_leafCount
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth) :
    cavityGeneratedComponentLeafCount (printedGeneratedOriginFutureChartComponent U γ j) =
      cavityGeneratedComponentLeafCount U + 2 := by
  rcases γ with i | (i | u)
  · let v := printedGeneratedOriginChartFork U i
    have hv := printedGeneratedOriginChartFork_interior U i
    have hd : min j.val (v.depth-1) < v.depth := by
      exact Nat.lt_of_le_of_lt (Nat.min_le_right j.val (v.depth-1)) (Nat.sub_lt hv.1 Nat.one_pos)
    exact printedGeneratedFutureVertexComponent_leafCount U v hv.1 hv.2 _ hd
  · exact nativeStreamingGeneratedSharedFutureEdgeComponent_leafCount U _ _ _
  · have hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
    have hj : j.val+1 < (nativeStreamingGeneratedEndpointVertex U (.root U.tree)).depth := by
      rw [nativeStreamingGeneratedEndpointVertex_depth]
      change j.val+1 < U.depth+1
      omega
    exact (printedGeneratedFutureVertexComponent_leafCount (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree)) hv.1 hv.2 (j.val+1) hj).trans
      (congrArg (fun L : ℕ => L+2) (printedGeneratedEndpointComponent_leafCount U))

end QuantitativeFollowup
