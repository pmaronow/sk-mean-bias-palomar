module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsClocks
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairProbabilityPhysical

@[expose] public section

/-! Four fixed two-slot charts preserve the original prefix and its edge cells.
Each chart has continuous labels; the chronological order is derived from its
actual restriction, including equal physical times. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

inductive NativeStreamingGeneratedCrossEdgeChart
  | lt | equal | gt | apart
  deriving DecidableEq, Fintype

namespace NativeStreamingGeneratedCrossEdgeChart

def firstSlot : NativeStreamingGeneratedCrossEdgeChart → ℕ
  | .lt => 1 | _ => 0

def secondSlot : NativeStreamingGeneratedCrossEdgeChart → ℕ
  | .gt => 1 | _ => 0

def Holds (c : NativeStreamingGeneratedCrossEdgeChart) (de df : ℕ)
    (r l : Paper.Overlap) : Prop :=
  match c with
  | .lt => de=df ∧ r<l
  | .equal => de=df ∧ r=l
  | .gt => de=df ∧ l<r
  | .apart => de≠df

theorem firstSlot_lt (c : NativeStreamingGeneratedCrossEdgeChart) : c.firstSlot<2 := by
  cases c <;> decide

theorem secondSlot_lt (c : NativeStreamingGeneratedCrossEdgeChart) : c.secondSlot<2 := by
  cases c <;> decide

theorem indices (c : NativeStreamingGeneratedCrossEdgeChart) (de df : ℕ)
    (r l : Paper.Overlap) (hc : c.Holds de df r l) :
    c.firstSlot=nativeStreamingPairObservationIndex de df r l ∧
      c.secondSlot=nativeStreamingPairObservationIndex df de l r := by
  cases c <;> simp only [Holds] at hc
  · rcases hc with ⟨he,hr⟩
    subst df
    simp [firstSlot,secondSlot,nativeStreamingPairObservationIndex,hr,not_lt_of_ge hr.le]
  · rcases hc with ⟨he,hr⟩
    subst df
    subst l
    simp [firstSlot,secondSlot,nativeStreamingPairObservationIndex]
  · rcases hc with ⟨he,hr⟩
    subst df
    simp [firstSlot,secondSlot,nativeStreamingPairObservationIndex,hr,not_lt_of_ge hr.le]
  · simp [firstSlot,secondSlot,nativeStreamingPairObservationIndex,hc,Ne.symm hc]

end NativeStreamingGeneratedCrossEdgeChart

def nativeStreamingGeneratedCrossEdgeFirstMark (m : ℕ) : Fin (m+2) := (Fin.last m).castSucc

def nativeStreamingGeneratedCrossEdgeSecondMark (m : ℕ) : Fin (m+2) := Fin.last (m+1)

def nativeStreamingGeneratedCrossEdgePrefix
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : CavityGeneratedHistory Paper.Overlap m :=
  cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)

def nativeStreamingGeneratedCrossEdgeAppend
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap) :
    CavityGeneratedHistory Paper.Overlap (m+2) := Fin.snoc (Fin.snoc h r) l

theorem nativeStreamingGeneratedCrossEdgePrefix_append
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap) :
    nativeStreamingGeneratedCrossEdgePrefix (nativeStreamingGeneratedCrossEdgeAppend h r l)=h := by
  simp only [nativeStreamingGeneratedCrossEdgePrefix,nativeStreamingGeneratedCrossEdgeAppend,
    cavityGeneratedHistoryPrefix_snoc]

theorem measurable_nativeStreamingGeneratedCrossEdgePrefix :
    Measurable (nativeStreamingGeneratedCrossEdgePrefix (m:=m)) :=
  cavityGeneratedHistoryPrefix_measurable.comp cavityGeneratedHistoryPrefix_measurable

theorem continuous_nativeStreamingGeneratedCrossEdgePrefix :
    Continuous (nativeStreamingGeneratedCrossEdgePrefix (m:=m)) :=
  continuous_pi (fun i => continuous_apply i.castSucc.castSucc)

def nativeStreamingGeneratedCrossEdgeGlobalLabels
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) (j : ℕ) : CavityGeneratedClockLabel (m+2) :=
  let old := (cavityGeneratedFiniteClockLabels W.label (j/3)).reindex
    (fun i => i.castSucc.castSucc)
  let R := CavityGeneratedClockLabel.mark (nativeStreamingGeneratedCrossEdgeFirstMark m)
  let L := CavityGeneratedClockLabel.mark (nativeStreamingGeneratedCrossEdgeSecondMark m)
  if j%3=0 then old
  else if e.depth=j/3 then
    if f.depth=j/3 then
      match c with
      | .lt => if j%3=1 then L else R
      | .gt => if j%3=1 then R else L
      | _ => R
    else R
  else if f.depth=j/3 then L else old

def nativeStreamingGeneratedCrossEdgeLabels
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (j : Fin (observationRefinementDepth nativeStreamingPairObservationSubdivision W.depth+1)) :
    CavityGeneratedClockLabel (m+2) := nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c j

theorem nativeStreamingGeneratedCrossEdgeGlobalLabels_refinement
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) (j : ℕ) :
    nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c
      (observationRefinementDepth nativeStreamingPairObservationSubdivision j)=
      (cavityGeneratedFiniteClockLabels W.label j).reindex (fun i => i.castSucc.castSucc) := by
  rw [nativeStreamingPairObservationSubdivision_depth]
  simp [nativeStreamingGeneratedCrossEdgeGlobalLabels]

theorem nativeStreamingGeneratedCrossEdgeLabels_global
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedCrossEdgeLabels W e f c)=
      nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c := by
  funext j
  by_cases hj : j≤observationRefinementDepth nativeStreamingPairObservationSubdivision W.depth
  · simp only [cavityGeneratedFiniteClockLabels,dif_pos hj,nativeStreamingGeneratedCrossEdgeLabels]
  · have hd := nativeStreamingPairObservationSubdivision_depth W.depth
    have he := e.depth_lt
    have hf := f.depth_lt
    have ho : W.depth≤j/3 := by omega
    have hold : cavityGeneratedFiniteClockLabels W.label (j/3)=.initial := by
      by_cases hb : j/3≤W.depth
      · have heq : j/3=W.depth := by omega
        rw [heq]
        simp only [cavityGeneratedFiniteClockLabels,dif_pos le_rfl]
        exact W.initial_label
      · simp only [cavityGeneratedFiniteClockLabels,dif_neg hb]
    have hne : e.depth≠j/3 := by omega
    have hnf : f.depth≠j/3 := by omega
    rw [cavityGeneratedFiniteClockLabels,dif_neg hj]
    simp only [nativeStreamingGeneratedCrossEdgeGlobalLabels,if_neg hne,if_neg hnf,hold,
      CavityGeneratedClockLabel.reindex]
    split_ifs <;> rfl

def nativeStreamingGeneratedCrossEdgeObservedComponent
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) : CavityGeneratedConstructedComponent (m+2) where
  depth := observationRefinementDepth nativeStreamingPairObservationSubdivision W.depth
  tree := observationRefineTree nativeStreamingPairObservationSubdivision W.tree
  label := nativeStreamingGeneratedCrossEdgeLabels W e f c
  terminal_label := by
    change nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c 0=.terminal
    simp only [nativeStreamingGeneratedCrossEdgeGlobalLabels,Nat.zero_mod,Nat.zero_div,ite_true,
      cavityGeneratedFiniteClockLabels,dif_pos (Nat.zero_le W.depth)]
    change (W.label 0).reindex (fun i => i.castSucc.castSucc)=.terminal
    rw [W.terminal_label]
    rfl
  initial_label := by
    change nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c
      (observationRefinementDepth nativeStreamingPairObservationSubdivision W.depth)=.initial
    rw [nativeStreamingGeneratedCrossEdgeGlobalLabels_refinement]
    simp only [cavityGeneratedFiniteClockLabels,dif_pos le_rfl]
    change (W.label (Fin.last W.depth)).reindex (fun i => i.castSucc.castSucc)=.initial
    rw [W.initial_label]
    rfl
  construction := by
    rw [nativeStreamingGeneratedCrossEdgeLabels_global]
    exact W.construction.refinement (fun i => i.castSucc.castSucc)
      nativeStreamingPairObservationSubdivision (nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c)
      (fun j _ => nativeStreamingGeneratedCrossEdgeGlobalLabels_refinement W e f c j)

private theorem crossEdge_oldLabel_append
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap) (j : ℕ) :
    ((cavityGeneratedFiniteClockLabels W.label j).reindex (fun i => i.castSucc.castSucc)).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      (cavityGeneratedFiniteClockLabels W.label j).value h := by
  cases cavityGeneratedFiniteClockLabels W.label j <;>
    simp [CavityGeneratedClockLabel.reindex,CavityGeneratedClockLabel.value,
      nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_castSucc]

theorem nativeStreamingGeneratedCrossEdgeGlobalLabels_append
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hc : c.Holds e.depth f.depth r l) (j : ℕ) :
    (nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c j).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      nativeStreamingPairObservationSchedule
        (fun p => (cavityGeneratedFiniteClockLabels W.label p).value h) e.depth f.depth r l j := by
  cases c <;> simp only [NativeStreamingGeneratedCrossEdgeChart.Holds] at hc
  all_goals
    simp only [nativeStreamingGeneratedCrossEdgeGlobalLabels,nativeStreamingPairObservationSchedule,
      nativeStreamingPairObservationTimes]
    split_ifs <;> simp_all only [crossEdge_oldLabel_append]
    all_goals simp_all [CavityGeneratedClockLabel.value,
      nativeStreamingGeneratedCrossEdgeAppend,nativeStreamingGeneratedCrossEdgeFirstMark,
      nativeStreamingGeneratedCrossEdgeSecondMark,Fin.snoc_castSucc,Fin.snoc_last,
      max_eq_left,max_eq_right,min_eq_left,min_eq_right] <;> order

theorem nativeStreamingGeneratedCrossEdgeObservedComponent_clock_append
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (f.depth+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h f.depth)
    (hc : c.Holds e.depth f.depth r l) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c)
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock W h) e.depth f.depth r l := by
  have he : (fun j => (nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c j).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l))=
      nativeStreamingPairObservationSchedule (nativeStreamingGeneratedComponentClock W h) e.depth f.depth r l := by
    funext j
    rw [nativeStreamingGeneratedCrossEdgeGlobalLabels_append W e f c h r l hc]
    congr 1
    funext p
    exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order W h hh p
  have hm := nativeStreamingPairObservationSchedule_antitone (nativeStreamingGeneratedComponentClock W h)
    (nativeStreamingGeneratedComponentClock_antitone W h) e.depth f.depth r l hr hl
  funext j
  change cavityGeneratedClippedClock
    (fun p => (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedCrossEdgeLabels W e f c) p).value
      (nativeStreamingGeneratedCrossEdgeAppend h r l)) j=_
  rw [nativeStreamingGeneratedCrossEdgeLabels_global,he]
  exact cavityGeneratedClippedClock_eq _ j (fun p _ => hm (Nat.le_succ p)) j le_rfl

end QuantitativeFollowup
