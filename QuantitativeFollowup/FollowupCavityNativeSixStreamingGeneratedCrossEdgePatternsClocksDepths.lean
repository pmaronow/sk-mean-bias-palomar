module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossEdgePatternsClocks

@[expose] public section

/-! Depth-only two-slot observation components. The second selected cell may
be an arbitrary future cell rather than the depth of an existing old edge. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def nativeStreamingGeneratedPairObservationGlobalLabels
    (W : CavityGeneratedConstructedComponent m) (de df : ℕ) (hde : de<W.depth) (hdf : df<W.depth)
    (c : NativeStreamingGeneratedCrossEdgeChart) (j : ℕ) : CavityGeneratedClockLabel (m+2) :=
  let old := (cavityGeneratedFiniteClockLabels W.label (j/3)).reindex
    (fun i => i.castSucc.castSucc)
  let R := CavityGeneratedClockLabel.mark (nativeStreamingGeneratedCrossEdgeFirstMark m)
  let L := CavityGeneratedClockLabel.mark (nativeStreamingGeneratedCrossEdgeSecondMark m)
  if j%3=0 then old
  else if de=j/3 then
    if df=j/3 then
      match c with
      | .lt => if j%3=1 then L else R
      | .gt => if j%3=1 then R else L
      | _ => R
    else R
  else if df=j/3 then L else old

def nativeStreamingGeneratedPairObservationLabels
    (W : CavityGeneratedConstructedComponent m) (de df : ℕ) (hde : de<W.depth) (hdf : df<W.depth)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (j : Fin (observationRefinementDepth nativeStreamingPairObservationSubdivision W.depth+1)) :
    CavityGeneratedClockLabel (m+2) := nativeStreamingGeneratedPairObservationGlobalLabels W de df hde hdf c j

theorem nativeStreamingGeneratedPairObservationGlobalLabels_refinement
    (W : CavityGeneratedConstructedComponent m) (de df : ℕ) (hde : de<W.depth) (hdf : df<W.depth)
    (c : NativeStreamingGeneratedCrossEdgeChart) (j : ℕ) :
    nativeStreamingGeneratedPairObservationGlobalLabels W de df hde hdf c
      (observationRefinementDepth nativeStreamingPairObservationSubdivision j)=
      (cavityGeneratedFiniteClockLabels W.label j).reindex (fun i => i.castSucc.castSucc) := by
  rw [nativeStreamingPairObservationSubdivision_depth]
  simp [nativeStreamingGeneratedPairObservationGlobalLabels]

theorem nativeStreamingGeneratedPairObservationLabels_global
    (W : CavityGeneratedConstructedComponent m) (de df : ℕ) (hde : de<W.depth) (hdf : df<W.depth)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedPairObservationLabels W de df hde hdf c)=
      nativeStreamingGeneratedPairObservationGlobalLabels W de df hde hdf c := by
  funext j
  by_cases hj : j≤observationRefinementDepth nativeStreamingPairObservationSubdivision W.depth
  · simp only [cavityGeneratedFiniteClockLabels,dif_pos hj,nativeStreamingGeneratedPairObservationLabels]
  · have hd := nativeStreamingPairObservationSubdivision_depth W.depth
    have he := hde
    have hf := hdf
    have ho : W.depth≤j/3 := by omega
    have hold : cavityGeneratedFiniteClockLabels W.label (j/3)=.initial := by
      by_cases hb : j/3≤W.depth
      · have heq : j/3=W.depth := by omega
        rw [heq]
        simp only [cavityGeneratedFiniteClockLabels,dif_pos le_rfl]
        exact W.initial_label
      · simp only [cavityGeneratedFiniteClockLabels,dif_neg hb]
    have hne : de≠j/3 := by omega
    have hnf : df≠j/3 := by omega
    rw [cavityGeneratedFiniteClockLabels,dif_neg hj]
    simp only [nativeStreamingGeneratedPairObservationGlobalLabels,if_neg hne,if_neg hnf,hold,
      CavityGeneratedClockLabel.reindex]
    split_ifs <;> rfl

def nativeStreamingGeneratedPairObservationComponent
    (W : CavityGeneratedConstructedComponent m) (de df : ℕ) (hde : de<W.depth) (hdf : df<W.depth)
    (c : NativeStreamingGeneratedCrossEdgeChart) : CavityGeneratedConstructedComponent (m+2) where
  depth := observationRefinementDepth nativeStreamingPairObservationSubdivision W.depth
  tree := observationRefineTree nativeStreamingPairObservationSubdivision W.tree
  label := nativeStreamingGeneratedPairObservationLabels W de df hde hdf c
  terminal_label := by
    change nativeStreamingGeneratedPairObservationGlobalLabels W de df hde hdf c 0=.terminal
    simp only [nativeStreamingGeneratedPairObservationGlobalLabels,Nat.zero_mod,Nat.zero_div,ite_true,
      cavityGeneratedFiniteClockLabels,dif_pos (Nat.zero_le W.depth)]
    change (W.label 0).reindex (fun i => i.castSucc.castSucc)=.terminal
    rw [W.terminal_label]
    rfl
  initial_label := by
    change nativeStreamingGeneratedPairObservationGlobalLabels W de df hde hdf c
      (observationRefinementDepth nativeStreamingPairObservationSubdivision W.depth)=.initial
    rw [nativeStreamingGeneratedPairObservationGlobalLabels_refinement]
    simp only [cavityGeneratedFiniteClockLabels,dif_pos le_rfl]
    change (W.label (Fin.last W.depth)).reindex (fun i => i.castSucc.castSucc)=.initial
    rw [W.initial_label]
    rfl
  construction := by
    rw [nativeStreamingGeneratedPairObservationLabels_global]
    exact W.construction.refinement (fun i => i.castSucc.castSucc)
      nativeStreamingPairObservationSubdivision (nativeStreamingGeneratedPairObservationGlobalLabels W de df hde hdf c)
      (fun j _ => nativeStreamingGeneratedPairObservationGlobalLabels_refinement W de df hde hdf c j)

private theorem pairObservation_oldLabel_append
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap) (j : ℕ) :
    ((cavityGeneratedFiniteClockLabels W.label j).reindex (fun i => i.castSucc.castSucc)).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      (cavityGeneratedFiniteClockLabels W.label j).value h := by
  cases cavityGeneratedFiniteClockLabels W.label j <;>
    simp [CavityGeneratedClockLabel.reindex,CavityGeneratedClockLabel.value,
      nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_castSucc]

theorem nativeStreamingGeneratedPairObservationGlobalLabels_append
    (W : CavityGeneratedConstructedComponent m) (de df : ℕ) (hde : de<W.depth) (hdf : df<W.depth)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hc : c.Holds de df r l) (j : ℕ) :
    (nativeStreamingGeneratedPairObservationGlobalLabels W de df hde hdf c j).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      nativeStreamingPairObservationSchedule
        (fun p => (cavityGeneratedFiniteClockLabels W.label p).value h) de df r l j := by
  cases c <;> simp only [NativeStreamingGeneratedCrossEdgeChart.Holds] at hc
  all_goals
    simp only [nativeStreamingGeneratedPairObservationGlobalLabels,nativeStreamingPairObservationSchedule,
      nativeStreamingPairObservationTimes]
    split_ifs <;> simp_all only [pairObservation_oldLabel_append]
    all_goals simp_all [CavityGeneratedClockLabel.value,
      nativeStreamingGeneratedCrossEdgeAppend,nativeStreamingGeneratedCrossEdgeFirstMark,
      nativeStreamingGeneratedCrossEdgeSecondMark,Fin.snoc_castSucc,Fin.snoc_last,
      max_eq_left,max_eq_right,min_eq_left,min_eq_right] <;> order

theorem nativeStreamingGeneratedPairObservationComponent_clock_append
    (W : CavityGeneratedConstructedComponent m) (de df : ℕ) (hde : de<W.depth) (hdf : df<W.depth)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (de+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h de)
    (hl : nativeStreamingGeneratedComponentClock W h (df+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h df)
    (hc : c.Holds de df r l) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedPairObservationComponent W de df hde hdf c)
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock W h) de df r l := by
  have he : (fun j => (nativeStreamingGeneratedPairObservationGlobalLabels W de df hde hdf c j).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l))=
      nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock W h) de df r l := by
    funext j
    rw [nativeStreamingGeneratedPairObservationGlobalLabels_append W de df hde hdf c h r l hc]
    congr 1
    funext p
    exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order W h hh p
  have hm := nativeStreamingPairObservationSchedule_antitone (nativeStreamingGeneratedComponentClock W h)
    (nativeStreamingGeneratedComponentClock_antitone W h) de df r l hr hl
  funext j
  change cavityGeneratedClippedClock
    (fun p => (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedPairObservationLabels W de df hde hdf c) p).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l)) j=_
  rw [nativeStreamingGeneratedPairObservationLabels_global,he]
  exact cavityGeneratedClippedClock_eq _ j (fun p _ => hm (Nat.le_succ p)) j le_rfl

theorem nativeStreamingGeneratedPairObservationComponent_eq_crossEdge
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    nativeStreamingGeneratedPairObservationComponent W e.depth f.depth e.depth_lt f.depth_lt c=
      nativeStreamingGeneratedCrossEdgeObservedComponent W e f c := rfl

end QuantitativeFollowup
