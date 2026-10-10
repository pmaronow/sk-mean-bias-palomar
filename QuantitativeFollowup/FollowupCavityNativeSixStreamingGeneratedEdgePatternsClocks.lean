module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsClocks
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeMarkLaw

@[expose] public section

/-! A free edge observation is a genuine unary refinement. Old labels are
retained at their literal refined depths, and only the inserted observation
uses the appended history coordinate. Physical clocks are derived from the
old order restriction and the actual closed edge cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def nativeStreamingGeneratedEdgeGlobalLabels
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) : CavityGeneratedClockLabel (m+1) :=
  if j≤e.depth then (cavityGeneratedFiniteClockLabels W.label j).reindex Fin.castSucc
  else if j=e.depth+1 then .mark (Fin.last m)
  else (cavityGeneratedFiniteClockLabels W.label (j-1)).reindex Fin.castSucc

def nativeStreamingGeneratedEdgeLabels
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : Fin (observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) W.depth+1)) :
    CavityGeneratedClockLabel (m+1) := nativeStreamingGeneratedEdgeGlobalLabels W e j

theorem nativeStreamingGeneratedEdgeGlobalLabels_refinement
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) (j : ℕ) :
    nativeStreamingGeneratedEdgeGlobalLabels W e
      (observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) j) =
        (cavityGeneratedFiniteClockLabels W.label j).reindex Fin.castSucc := by
  rw [nativeStreamingEdgeSubdivision_depth]
  unfold nativeStreamingGeneratedEdgeGlobalLabels
  split_ifs <;> simp_all <;> omega

theorem nativeStreamingGeneratedEdgeLabels_global
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels W e) =
      nativeStreamingGeneratedEdgeGlobalLabels W e := by
  funext j
  have he := e.depth_lt
  have hd : observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) W.depth =
      W.depth+1 := by rw [nativeStreamingEdgeSubdivision_depth, if_neg (by omega)]
  by_cases hj : j≤observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) W.depth
  · simp only [cavityGeneratedFiniteClockLabels,dif_pos hj,nativeStreamingGeneratedEdgeLabels]
  · rw [hd] at hj
    have hje : ¬j≤e.depth := by omega
    have hjn : j≠e.depth+1 := by omega
    have hjold : ¬j-1≤W.depth := by omega
    simp only [cavityGeneratedFiniteClockLabels,hd,dif_neg hj,
      nativeStreamingGeneratedEdgeGlobalLabels,if_neg hje,if_neg hjn,dif_neg hjold,
      CavityGeneratedClockLabel.reindex]

def nativeStreamingGeneratedEdgeObservedComponent
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    CavityGeneratedConstructedComponent (m+1) where
  depth := observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) W.depth
  tree := observationRefineTree (nativeStreamingEdgeSubdivision e.depth) W.tree
  label := nativeStreamingGeneratedEdgeLabels W e
  terminal_label := by
    change nativeStreamingGeneratedEdgeGlobalLabels W e 0=.terminal
    simp only [nativeStreamingGeneratedEdgeGlobalLabels, Nat.zero_le, if_pos,
      cavityGeneratedFiniteClockLabels,dif_pos (Nat.zero_le W.depth)]
    change (W.label 0).reindex Fin.castSucc=.terminal
    rw [W.terminal_label]
    rfl
  initial_label := by
    change nativeStreamingGeneratedEdgeGlobalLabels W e
      (observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) W.depth)=.initial
    rw [nativeStreamingGeneratedEdgeGlobalLabels_refinement]
    simp only [cavityGeneratedFiniteClockLabels,dif_pos le_rfl]
    change (W.label (Fin.last W.depth)).reindex Fin.castSucc=.initial
    rw [W.initial_label]
    rfl
  construction := by
    rw [nativeStreamingGeneratedEdgeLabels_global]
    exact W.construction.refinement Fin.castSucc (nativeStreamingEdgeSubdivision e.depth)
      (nativeStreamingGeneratedEdgeGlobalLabels W e)
      (fun j _ => nativeStreamingGeneratedEdgeGlobalLabels_refinement W e j)

theorem nativeStreamingGeneratedEdgeObservedComponent_depth
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    (nativeStreamingGeneratedEdgeObservedComponent W e).depth=W.depth+1 := by
  change observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) W.depth=W.depth+1
  rw [nativeStreamingEdgeSubdivision_depth,if_neg (by have he:=e.depth_lt; omega)]

def nativeStreamingGeneratedEdgeVertex
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    FiniteCascadeRecordVertex (nativeStreamingGeneratedEdgeObservedComponent W e).tree :=
  nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e

theorem nativeStreamingGeneratedEdgeVertex_depth
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    (nativeStreamingGeneratedEdgeVertex W e).depth=e.depth+1 :=
  nativeStreamingEdgeRefinedVertex_inserted_depth e

theorem nativeStreamingGeneratedEdgeVertex_interior
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    0<(nativeStreamingGeneratedEdgeVertex W e).depth ∧
      (nativeStreamingGeneratedEdgeVertex W e).depth<
        (nativeStreamingGeneratedEdgeObservedComponent W e).depth := by
  rw [nativeStreamingGeneratedEdgeVertex_depth,nativeStreamingGeneratedEdgeObservedComponent_depth]
  have he:=e.depth_lt
  omega

theorem nativeStreamingGeneratedEdgeVertex_label
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeObservedComponent W e).label
      (nativeStreamingGeneratedEdgeVertex W e).depth = .mark (Fin.last m) := by
  change cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels W e) _ = _
  rw [nativeStreamingGeneratedEdgeLabels_global,nativeStreamingGeneratedEdgeVertex_depth]
  simp only [nativeStreamingGeneratedEdgeGlobalLabels,if_neg (by omega : ¬e.depth+1≤e.depth),
    ite_true]

theorem nativeStreamingGeneratedEdgeGlobalLabels_snoc_value
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) (j : ℕ) :
    (nativeStreamingGeneratedEdgeGlobalLabels W e j).value (Fin.snoc h r) =
      nativeStreamingEdgeSchedule
        (fun p => (cavityGeneratedFiniteClockLabels W.label p).value h) e.depth r j := by
  unfold nativeStreamingGeneratedEdgeGlobalLabels nativeStreamingEdgeSchedule
  split_ifs
  · rw [CavityGeneratedClockLabel.append_reindex_value,cavityGeneratedHistoryPrefix_snoc]
  · simp only [CavityGeneratedClockLabel.value,Fin.snoc_last]
  · rw [CavityGeneratedClockLabel.append_reindex_value,cavityGeneratedHistoryPrefix_snoc]

theorem nativeStreamingGeneratedComponent_raw_eq_clock_of_order
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W) (j : ℕ) :
    (cavityGeneratedFiniteClockLabels W.label j).value h=
      nativeStreamingGeneratedComponentClock W h j := by
  by_cases hj : j≤W.depth
  · exact (nativeStreamingGeneratedComponentClock_eq_label_of_mem W h hh j hj).symm
  · rw [nativeStreamingGeneratedComponentClock_after_initial W h j (by omega)]
    simp only [cavityGeneratedFiniteClockLabels,dif_neg hj,CavityGeneratedClockLabel.value]

theorem nativeStreamingGeneratedEdgeObservedComponent_clock_snoc
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e)
      (Fin.snoc h r)=nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock W h) e.depth r := by
  have he : (fun j => (nativeStreamingGeneratedEdgeGlobalLabels W e j).value (Fin.snoc h r)) =
      nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock W h) e.depth r := by
    funext j
    rw [nativeStreamingGeneratedEdgeGlobalLabels_snoc_value]
    congr 1
    funext p
    exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order W h hh p
  have hmono := nativeStreamingEdgeSchedule_antitone
    (nativeStreamingGeneratedComponentClock W h)
    (nativeStreamingGeneratedComponentClock_antitone W h) e.depth r hr
  funext j
  change cavityGeneratedClippedClock
    (fun p => (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels W e) p).value
      (Fin.snoc h r)) j = _
  rw [nativeStreamingGeneratedEdgeLabels_global,he]
  exact cavityGeneratedClippedClock_eq _ j (fun p _ => hmono (Nat.le_succ p)) j le_rfl

end QuantitativeFollowup
