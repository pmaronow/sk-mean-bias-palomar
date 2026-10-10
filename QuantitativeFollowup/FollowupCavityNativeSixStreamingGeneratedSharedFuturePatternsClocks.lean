module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsClocks
public import QuantitativeFollowup.FollowupCavityGeneratedRetainedVertexGraft

@[expose] public section

/-! A genuine free observation supplies the shared future split. The old
anchor stays at its embedded vertex and the inserted mark is used directly
by both descendants, without a second atom draw at that mark. -/

noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def nativeStreamingGeneratedSharedFutureAnchor
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree) :
    FiniteCascadeRecordVertex (nativeStreamingGeneratedEdgeObservedComponent W e).tree :=
  nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) W.tree v

theorem nativeStreamingGeneratedSharedFutureAnchor_depth
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (hj : e.depth < v.depth) :
    (nativeStreamingGeneratedSharedFutureAnchor W v e).depth = v.depth+1 := by
  rw [nativeStreamingGeneratedSharedFutureAnchor,
    nativeStreamingRefinementVertexEmbed_depth,nativeStreamingEdgeSubdivision_depth,
    if_neg (not_le.mpr hj)]

theorem nativeStreamingGeneratedSharedFutureAnchor_label
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeObservedComponent W e).label
      (nativeStreamingGeneratedSharedFutureAnchor W v e).depth = .mark b.castSucc := by
  change cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels W e)
    (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth)
      W.tree v).depth = _
  rw [nativeStreamingGeneratedEdgeLabels_global,nativeStreamingRefinementVertexEmbed_depth,
    nativeStreamingGeneratedEdgeGlobalLabels_refinement,hb]
  rfl

theorem nativeStreamingGeneratedSharedFuture_split_label
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeObservedComponent W e).label
      (e.depth+1) = .mark (Fin.last m) := by
  simpa only [nativeStreamingGeneratedEdgeVertex_depth] using
    nativeStreamingGeneratedEdgeVertex_label W e

theorem nativeStreamingGeneratedSharedFuture_split_le_anchor
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (hj : e.depth < v.depth) :
    e.depth+1 ≤ (nativeStreamingGeneratedSharedFutureAnchor W v e).depth := by
  rw [nativeStreamingGeneratedSharedFutureAnchor_depth W v e hj]
  omega

def nativeStreamingGeneratedSharedFutureComponent
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    CavityGeneratedConstructedComponent (m+1) :=
  nativeStreamingGeneratedRetainedFutureComponent
    (nativeStreamingGeneratedEdgeObservedComponent W e)
    (nativeStreamingGeneratedSharedFutureAnchor W v e) b.castSucc
    (nativeStreamingGeneratedSharedFutureAnchor_label W v b hb e)
    (e.depth+1) (nativeStreamingGeneratedSharedFuture_split_le_anchor W v e hj)
    (Fin.last m) (nativeStreamingGeneratedSharedFuture_split_label W e)

theorem nativeStreamingGeneratedSharedFutureComponent_clock
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj) H =
      nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e) H := rfl

theorem nativeStreamingGeneratedSharedFutureComponent_clock_snoc
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj) (Fin.snoc h r) =
      nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock W h) e.depth r := by
  rw [nativeStreamingGeneratedSharedFutureComponent_clock,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr]

theorem nativeStreamingGeneratedSharedFuture_split_clock
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj) (Fin.snoc h r)
        (e.depth+1) = r := by
  rw [nativeStreamingGeneratedSharedFutureComponent_clock_snoc W v b hb e hj h r hh hr,
    nativeStreamingEdgeSchedule_inserted]

end QuantitativeFollowup
