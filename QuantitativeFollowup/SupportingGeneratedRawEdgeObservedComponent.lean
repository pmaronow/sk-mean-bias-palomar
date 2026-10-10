module
public import QuantitativeFollowup.SupportingGeneratedRawVertexGraftComponent
public import QuantitativeFollowup.SupportingGeneratedRawRefinementForkProvenance

@[expose] public section

/-! A raw source edge inserts its actual selected physical time. The
observation refinement retains every inherited fork index, and computed
support gives the genuine inserted clock without restricting unary clocks
to history coordinates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedObservedRawEdgeObservedComponent
    (U : CavityGeneratedObservedRawComponent m) (e : NativeStreamingEdge U.tree) :
    CavityGeneratedObservedRawComponent (m+1) where
  depth := observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) U.depth
  tree := observationRefineTree (nativeStreamingEdgeSubdivision e.depth) U.tree
  rawClock H := nativeStreamingEdgeSchedule (U.clock (cavityGeneratedHistoryPrefix H))
    e.depth (H (Fin.last m))
  measurable_rawClock j := by
    unfold nativeStreamingEdgeSchedule
    split_ifs
    · exact (U.measurable_clock _).comp (measurable_pi_iff.mpr fun i=>measurable_pi_apply i.castSucc)
    · exact measurable_pi_apply (Fin.last m)
    · exact (U.measurable_clock _).comp (measurable_pi_iff.mpr fun i=>measurable_pi_apply i.castSucc)
  rawClock_terminal H := by
    change nativeStreamingEdgeSchedule _ e.depth _ 0=1
    simp only [nativeStreamingEdgeSchedule,Nat.zero_le,ite_true]
    exact U.clock_terminal _
  rawClock_initial H := by
    rw [nativeStreamingEdgeSchedule_refinement]
    exact U.clock_initial _
  forkMark i := (U.forkMark (Fin.cast
    (cavityGeneratedRawRefinementForkCount (nativeStreamingEdgeSubdivision e.depth) U.tree) i)).castSucc

/-- The inserted schedule is already antitone on its actual closed cell. -/
theorem cavityGeneratedObservedRawEdgeObservedComponent_clock
    (U : CavityGeneratedObservedRawComponent m) (e : NativeStreamingEdge U.tree)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (hr : U.clock (cavityGeneratedHistoryPrefix H) (e.depth+1)≤H (Fin.last m) ∧
      H (Fin.last m)≤U.clock (cavityGeneratedHistoryPrefix H) e.depth) :
    (cavityGeneratedObservedRawEdgeObservedComponent U e).clock H =
      nativeStreamingEdgeSchedule (U.clock (cavityGeneratedHistoryPrefix H)) e.depth (H (Fin.last m)) := by
  have hq := nativeStreamingEdgeSchedule_antitone (U.clock (cavityGeneratedHistoryPrefix H))
    (U.clock_antitone _) e.depth (H (Fin.last m)) hr
  funext j
  exact cavityGeneratedClippedClock_eq _ j (fun i _=>hq (Nat.le_succ i)) j le_rfl

/-- Every original fork keeps its original retained mark, in its actual list order. -/
theorem cavityGeneratedObservedRawEdgeObservedComponent_support
    (U : CavityGeneratedObservedRawComponent m) (e : NativeStreamingEdge U.tree)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (hh : cavityGeneratedHistoryPrefix H∈U.supportSet)
    (hr : U.clock (cavityGeneratedHistoryPrefix H) (e.depth+1)≤H (Fin.last m) ∧
      H (Fin.last m)≤U.clock (cavityGeneratedHistoryPrefix H) e.depth) :
    H∈(cavityGeneratedObservedRawEdgeObservedComponent U e).supportSet := by
  constructor
  · intro j
    exact nativeStreamingEdgeSchedule_antitone (U.clock (cavityGeneratedHistoryPrefix H))
      (U.clock_antitone _) e.depth (H (Fin.last m)) hr (Nat.le_succ j.val)
  · intro i
    let d := nativeStreamingEdgeSubdivision e.depth
    let j := Fin.cast (cavityGeneratedRawRefinementForkCount d U.tree) i
    have hji : Fin.cast (cavityGeneratedRawRefinementForkCount d U.tree).symm j=i := by
      apply Fin.ext
      rfl
    have hd := cavityGeneratedRawRefinementForkIndex_depth d U.tree j
    rw [hji] at hd
    change nativeStreamingEdgeSchedule (U.clock (cavityGeneratedHistoryPrefix H)) e.depth (H (Fin.last m))
      ((cavityGeneratedOriginForkVertices (observationRefineTree d U.tree)).get i).depth =
        H (U.forkMark j).castSucc
    rw [hd,nativeStreamingEdgeSchedule_refinement]
    exact U.fork_clock_is_mark (cavityGeneratedHistoryPrefix H) hh j

/-- The selected actual retained state is at the newly appended physical time. -/
theorem cavityGeneratedObservedRawEdgeObservedComponent_selected_clock
    (U : CavityGeneratedObservedRawComponent m) (e : NativeStreamingEdge U.tree)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (hr : U.clock (cavityGeneratedHistoryPrefix H) (e.depth+1)≤H (Fin.last m) ∧
      H (Fin.last m)≤U.clock (cavityGeneratedHistoryPrefix H) e.depth) :
    (cavityGeneratedObservedRawEdgeObservedComponent U e).clock H
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e).depth = H (Fin.last m) := by
  rw [cavityGeneratedObservedRawEdgeObservedComponent_clock U e H hr]
  exact nativeStreamingEdgeRefinedVertex_inserted_level _ e _

def cavityGeneratedObservedRawEdgeGraftComponent
    (U : CavityGeneratedObservedRawComponent m) (e : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedVertexKind) : CavityGeneratedObservedRawComponent (m+1) :=
  cavityGeneratedObservedRawVertexGraftComponent (cavityGeneratedObservedRawEdgeObservedComponent U e)
    (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e) (Fin.last m) k

theorem cavityGeneratedObservedRawEdgeGraftComponent_support
    (U : CavityGeneratedObservedRawComponent m) (e : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedVertexKind) (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (hh : cavityGeneratedHistoryPrefix H∈U.supportSet)
    (hr : U.clock (cavityGeneratedHistoryPrefix H) (e.depth+1)≤H (Fin.last m) ∧
      H (Fin.last m)≤U.clock (cavityGeneratedHistoryPrefix H) e.depth) :
    H∈(cavityGeneratedObservedRawEdgeGraftComponent U e k).supportSet := by
  exact cavityGeneratedObservedRawVertexGraftComponent_support _ _ _ k H
    (cavityGeneratedObservedRawEdgeObservedComponent_support U e H hh hr)
    (cavityGeneratedObservedRawEdgeObservedComponent_selected_clock U e H hr).symm

theorem cavityGeneratedObservedRawEdgeGraftComponent_clock
    (U : CavityGeneratedObservedRawComponent m) (e : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedVertexKind) (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (hr : U.clock (cavityGeneratedHistoryPrefix H) (e.depth+1)≤H (Fin.last m) ∧
      H (Fin.last m)≤U.clock (cavityGeneratedHistoryPrefix H) e.depth) :
    (cavityGeneratedObservedRawEdgeGraftComponent U e k).clock H=
      nativeStreamingEdgeSchedule (U.clock (cavityGeneratedHistoryPrefix H)) e.depth (H (Fin.last m)) :=
  cavityGeneratedObservedRawEdgeObservedComponent_clock U e H hr

end QuantitativeFollowup
