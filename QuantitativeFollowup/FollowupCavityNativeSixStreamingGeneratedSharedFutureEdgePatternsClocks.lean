module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossEdgePatternsClocksDepths
public import QuantitativeFollowup.FollowupCavityGeneratedRetainedVertexGraft

@[expose] public section

/-! Two genuine free marks, sampled on the original prefix, supply the
incident edge ancestor and its shared future split.  The same-cell strict
future chart uses the later observation before the earlier one. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def nativeStreamingGeneratedSharedFutureEdgeChart (de j : ℕ) :
    NativeStreamingGeneratedCrossEdgeChart := if j=de then .lt else .apart

theorem nativeStreamingGeneratedSharedFutureEdgeChart_holds
    (de j : ℕ) (r l : Paper.Overlap) (hrl : r<l) :
    (nativeStreamingGeneratedSharedFutureEdgeChart de j).Holds de j r l := by
  by_cases he : j=de
  · simp only [nativeStreamingGeneratedSharedFutureEdgeChart,if_pos he,
      NativeStreamingGeneratedCrossEdgeChart.Holds]
    exact ⟨he.symm,hrl⟩
  · simp only [nativeStreamingGeneratedSharedFutureEdgeChart,if_neg he,
      NativeStreamingGeneratedCrossEdgeChart.Holds]
    exact Ne.symm he

def nativeStreamingGeneratedSharedFutureEdgeObserved
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) : CavityGeneratedConstructedComponent (m+2) :=
  nativeStreamingGeneratedPairObservationComponent W e.depth j e.depth_lt
    (lt_of_le_of_lt hj e.depth_lt) (nativeStreamingGeneratedSharedFutureEdgeChart e.depth j)

def nativeStreamingGeneratedSharedFutureEdgeAnchor
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    FiniteCascadeRecordVertex (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj).tree :=
  nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
    (nativeStreamingGeneratedSharedFutureEdgeChart e.depth j).firstSlot

def nativeStreamingGeneratedSharedFutureEdgeSplit (de j : ℕ) : ℕ :=
  observationRefinementDepth nativeStreamingPairObservationSubdivision j+
    (nativeStreamingGeneratedSharedFutureEdgeChart de j).secondSlot+1

theorem nativeStreamingGeneratedSharedFutureEdge_split_le_anchor
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j≤
      (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj).depth := by
  rw [nativeStreamingGeneratedSharedFutureEdgeAnchor,nativeStreamingEdgeSelectedVertex_depth
    _ e _ (NativeStreamingGeneratedCrossEdgeChart.firstSlot_lt _)]
  simp only [nativeStreamingGeneratedSharedFutureEdgeSplit,
    nativeStreamingPairObservationSubdivision_depth]
  by_cases he : j=e.depth
  · simp only [nativeStreamingGeneratedSharedFutureEdgeChart,if_pos he,
      NativeStreamingGeneratedCrossEdgeChart.firstSlot,NativeStreamingGeneratedCrossEdgeChart.secondSlot]
    omega
  · simp only [nativeStreamingGeneratedSharedFutureEdgeChart,if_neg he,
      NativeStreamingGeneratedCrossEdgeChart.firstSlot,NativeStreamingGeneratedCrossEdgeChart.secondSlot]
    omega

theorem nativeStreamingGeneratedSharedFutureEdge_anchor_label
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj).label
      (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj).depth=
        .mark (nativeStreamingGeneratedCrossEdgeFirstMark m) := by
  change cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedPairObservationLabels W e.depth j
    e.depth_lt (lt_of_le_of_lt hj e.depth_lt) (nativeStreamingGeneratedSharedFutureEdgeChart e.depth j))
      (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
        (nativeStreamingGeneratedSharedFutureEdgeChart e.depth j).firstSlot).depth=_
  rw [nativeStreamingGeneratedPairObservationLabels_global,nativeStreamingEdgeSelectedVertex_depth
    _ e _ (NativeStreamingGeneratedCrossEdgeChart.firstSlot_lt _),
    nativeStreamingPairObservationSubdivision_depth]
  have hd1 : (3*e.depth+0+1)/3=e.depth := by omega
  have hm1 : (3*e.depth+0+1)%3=1 := by omega
  have hd2 : (3*e.depth+1+1)/3=e.depth := by omega
  have hm2 : (3*e.depth+1+1)%3=2 := by omega
  by_cases he : j=e.depth
  · simp [nativeStreamingGeneratedSharedFutureEdgeChart,he,
      NativeStreamingGeneratedCrossEdgeChart.firstSlot,
      nativeStreamingGeneratedPairObservationGlobalLabels,hd2,hm2]
  · simp [nativeStreamingGeneratedSharedFutureEdgeChart,he,
      NativeStreamingGeneratedCrossEdgeChart.firstSlot,
      nativeStreamingGeneratedPairObservationGlobalLabels,hd1,hm1]

theorem nativeStreamingGeneratedSharedFutureEdge_split_label
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj).label
      (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)=
        .mark (nativeStreamingGeneratedCrossEdgeSecondMark m) := by
  change cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedPairObservationLabels W e.depth j
    e.depth_lt (lt_of_le_of_lt hj e.depth_lt) (nativeStreamingGeneratedSharedFutureEdgeChart e.depth j)) _=_
  rw [nativeStreamingGeneratedPairObservationLabels_global]
  have hd : (3*j+0+1)/3=j := by omega
  have hm : (3*j+0+1)%3=1 := by omega
  have hde : (3*e.depth+1)/3=e.depth := by omega
  have hme : (3*e.depth+1)%3=1 := by omega
  by_cases he : j=e.depth
  · simp [nativeStreamingGeneratedSharedFutureEdgeSplit,
      nativeStreamingPairObservationSubdivision_depth,nativeStreamingGeneratedSharedFutureEdgeChart,
      he,NativeStreamingGeneratedCrossEdgeChart.secondSlot,
      nativeStreamingGeneratedPairObservationGlobalLabels,hde,hme]
  · simp [nativeStreamingGeneratedSharedFutureEdgeSplit,
      nativeStreamingPairObservationSubdivision_depth,nativeStreamingGeneratedSharedFutureEdgeChart,
      he,Ne.symm he,NativeStreamingGeneratedCrossEdgeChart.secondSlot,
      nativeStreamingGeneratedPairObservationGlobalLabels,hd,hm]

def nativeStreamingGeneratedSharedFutureEdgeComponent
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) : CavityGeneratedConstructedComponent (m+2) :=
  nativeStreamingGeneratedRetainedFutureComponent
    (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj)
    (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
    (nativeStreamingGeneratedCrossEdgeFirstMark m)
    (nativeStreamingGeneratedSharedFutureEdge_anchor_label W e j hj)
    (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)
    (nativeStreamingGeneratedSharedFutureEdge_split_le_anchor W e j hj)
    (nativeStreamingGeneratedCrossEdgeSecondMark m)
    (nativeStreamingGeneratedSharedFutureEdge_split_label W e j hj)

theorem nativeStreamingGeneratedSharedFutureEdgeComponent_clock
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj) H=
      nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj) H := rfl

theorem nativeStreamingGeneratedSharedFutureEdgeObserved_clock_append
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (j+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h j)
    (hrl : r<l) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj)
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock W h) e.depth j r l :=
  nativeStreamingGeneratedPairObservationComponent_clock_append W e.depth j e.depth_lt
    (lt_of_le_of_lt hj e.depth_lt) _ h r l hh hr hl
    (nativeStreamingGeneratedSharedFutureEdgeChart_holds e.depth j r l hrl)

theorem nativeStreamingGeneratedSharedFutureEdge_split_clock
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (j+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h j)
    (hrl : r<l) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj)
      (nativeStreamingGeneratedCrossEdgeAppend h r l) (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)=l := by
  rw [nativeStreamingGeneratedSharedFutureEdgeComponent_clock,
    nativeStreamingGeneratedSharedFutureEdgeObserved_clock_append W e j hj h r l hh hr hl hrl]
  have hi := (NativeStreamingGeneratedCrossEdgeChart.indices _ e.depth j r l
    (nativeStreamingGeneratedSharedFutureEdgeChart_holds e.depth j r l hrl)).2
  unfold nativeStreamingGeneratedSharedFutureEdgeSplit
  rw [hi]
  exact nativeStreamingPairObservationIndex_second_level _ e.depth j r l

end QuantitativeFollowup
