module
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossObservation
public import QuantitativeFollowup.SupportingGeneratedRawRefinementComponent
public import QuantitativeFollowup.SupportingGeneratedRawVertexGraftComponent

@[expose] public section

/-! The concrete raw cross output refines the original observation mesh
and adds two actual single continuations. All retained fork coordinates,
output support and the exact two-leaf increase are computed internally. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedRawCrossPrefix (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    CavityGeneratedHistory Paper.Overlap m := fun i=>H i.castSucc.castSucc

def cavityGeneratedRawCrossAppend (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap) :
    CavityGeneratedHistory Paper.Overlap (m+2) := Fin.snoc (Fin.snoc h r) l

def cavityGeneratedRawCrossFirstMark (m : ℕ) : Fin (m+2) := (Fin.last m).castSucc

def cavityGeneratedRawCrossSecondMark (m : ℕ) : Fin (m+2) := Fin.last (m+1)

theorem cavityGeneratedRawCrossPrefix_append (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap) : cavityGeneratedRawCrossPrefix (cavityGeneratedRawCrossAppend h r l)=h := by
  funext i
  simp [cavityGeneratedRawCrossPrefix,cavityGeneratedRawCrossAppend,Fin.snoc_castSucc]

private theorem rawCross_measurableObservationClock {Ω : Type*} [MeasurableSpace Ω]
    {J : ℕ} (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (q : Ω → ℕ → Paper.Overlap) (hq : ∀j, Measurable (fun h=>q h j))
    (r l : Ω → Paper.Overlap) (hr : Measurable r) (hl : Measurable l) (j : ℕ) :
    Measurable (fun h=>cavityGeneratedRawCrossObservationClock T s t (q h) (r h) (l h) j) := by
  rcases s with v | e <;> rcases t with w | f
  · exact hq j
  · change Measurable (fun h=>nativeStreamingEdgeSchedule (q h) f.depth (l h) j)
    unfold nativeStreamingEdgeSchedule
    split_ifs <;> first | exact hq _ | exact hl
  · change Measurable (fun h=>nativeStreamingEdgeSchedule (q h) e.depth (r h) j)
    unfold nativeStreamingEdgeSchedule
    split_ifs <;> first | exact hq _ | exact hr
  · change Measurable (fun h=>nativeStreamingPairObservationSchedule (q h) e.depth f.depth (r h) (l h) j)
    unfold nativeStreamingPairObservationSchedule nativeStreamingPairObservationTimes
    split_ifs <;> first | exact hq _ | exact hr.max hl | exact hr.min hl | exact hr | exact hl

def cavityGeneratedRawCrossComponentClock (U : CavityGeneratedObservedRawComponent m)
    (s t : CavityGeneratedRawCrossSite U.tree)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℕ → Paper.Overlap :=
  cavityGeneratedRawCrossObservationClock U.tree s t (U.clock (cavityGeneratedRawCrossPrefix H))
    (H (cavityGeneratedRawCrossFirstMark m)) (H (cavityGeneratedRawCrossSecondMark m))

theorem measurable_cavityGeneratedRawCrossComponentClock
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (j : ℕ) : Measurable (fun H=>cavityGeneratedRawCrossComponentClock U s t H j) := by
  have hp : Measurable (cavityGeneratedRawCrossPrefix (m:=m)) :=
    measurable_pi_iff.mpr fun i=>measurable_pi_apply i.castSucc.castSucc
  exact rawCross_measurableObservationClock U.tree s t
    (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>U.clock (cavityGeneratedRawCrossPrefix H))
    (fun j=>(U.measurable_clock j).comp hp)
    (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>H (cavityGeneratedRawCrossFirstMark m))
    (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>H (cavityGeneratedRawCrossSecondMark m))
    (measurable_pi_apply _) (measurable_pi_apply _) j

theorem cavityGeneratedRawCrossComponentClock_terminal
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : cavityGeneratedRawCrossComponentClock U s t H 0=1 :=
  (cavityGeneratedRawCrossObservation_refinement U.tree s t
    (U.clock (cavityGeneratedRawCrossPrefix H)) (H (cavityGeneratedRawCrossFirstMark m))
    (H (cavityGeneratedRawCrossSecondMark m)) 0).trans (U.clock_terminal _)

theorem cavityGeneratedRawCrossComponentClock_initial
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    cavityGeneratedRawCrossComponentClock U s t H
      (observationRefinementDepth (cavityGeneratedRawCrossSubdivision U.tree s t) U.depth)=0 :=
  (cavityGeneratedRawCrossObservation_refinement U.tree s t
    (U.clock (cavityGeneratedRawCrossPrefix H)) (H (cavityGeneratedRawCrossFirstMark m))
    (H (cavityGeneratedRawCrossSecondMark m)) U.depth).trans (U.clock_initial _)

def cavityGeneratedObservedRawCrossObservedComponent
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree) :
    CavityGeneratedObservedRawComponent (m+2) :=
  cavityGeneratedRawRefinementComponent U (cavityGeneratedRawCrossSubdivision U.tree s t)
    (cavityGeneratedRawCrossComponentClock U s t) (measurable_cavityGeneratedRawCrossComponentClock U s t)
    (cavityGeneratedRawCrossComponentClock_terminal U s t)
    (cavityGeneratedRawCrossComponentClock_initial U s t) (fun i=>i.castSucc.castSucc)

def cavityGeneratedObservedRawCrossComponent
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) : CavityGeneratedObservedRawComponent (m+2) :=
  let R := cavityGeneratedObservedRawCrossObservedComponent U s t
  let v := cavityGeneratedRawCrossObservationFirst U.tree s t k
  let w := cavityGeneratedRawCrossObservationSecond U.tree s t k
  let A := cavityGeneratedObservedRawVertexGraftComponent R v (cavityGeneratedRawCrossFirstMark m) .single
  cavityGeneratedObservedRawVertexGraftComponent A
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w)
    (cavityGeneratedRawCrossSecondMark m) .single

theorem cavityGeneratedRawCrossComponentClock_append
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap) :
    cavityGeneratedRawCrossComponentClock U s t (cavityGeneratedRawCrossAppend h r l)=
      cavityGeneratedRawCrossObservationClock U.tree s t (U.clock h) r l := by
  unfold cavityGeneratedRawCrossComponentClock
  rw [cavityGeneratedRawCrossPrefix_append]
  simp only [cavityGeneratedRawCrossFirstMark,cavityGeneratedRawCrossSecondMark,cavityGeneratedRawCrossAppend,
    Fin.snoc_castSucc,Fin.snoc_last]

theorem cavityGeneratedObservedRawCrossObservedComponent_support
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈U.supportSet) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (U.clock h) U.tree s r)
    (hl : cavityGeneratedRawCrossCell (U.clock h) U.tree t l) :
    cavityGeneratedRawCrossAppend h r l∈(cavityGeneratedObservedRawCrossObservedComponent U s t).supportSet := by
  apply cavityGeneratedRawRefinementComponent_support U
    (cavityGeneratedRawCrossSubdivision U.tree s t) (cavityGeneratedRawCrossComponentClock U s t)
    (measurable_cavityGeneratedRawCrossComponentClock U s t)
    (cavityGeneratedRawCrossComponentClock_terminal U s t)
    (cavityGeneratedRawCrossComponentClock_initial U s t) (fun i=>i.castSucc.castSucc) h _ hh
  · rw [cavityGeneratedRawCrossComponentClock_append]
    exact cavityGeneratedRawCrossObservation_antitone U.tree s t (U.clock h) (U.clock_antitone h) r l hr hl
  · intro j
    rw [cavityGeneratedRawCrossComponentClock_append]
    exact cavityGeneratedRawCrossObservation_refinement U.tree s t (U.clock h) r l j
  · intro i
    simp only [cavityGeneratedRawCrossAppend,Fin.snoc_castSucc]

theorem cavityGeneratedObservedRawCrossComponent_clock_append
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (U.clock h) U.tree s r)
    (hl : cavityGeneratedRawCrossCell (U.clock h) U.tree t l) :
    (cavityGeneratedObservedRawCrossComponent U s t k).clock (cavityGeneratedRawCrossAppend h r l)=
      cavityGeneratedRawCrossObservationClock U.tree s t (U.clock h) r l := by
  change cavityGeneratedClippedClock
    (cavityGeneratedRawCrossComponentClock U s t (cavityGeneratedRawCrossAppend h r l))=_
  rw [cavityGeneratedRawCrossComponentClock_append]
  funext j
  exact cavityGeneratedClippedClock_eq _ j
    (fun i _=>(cavityGeneratedRawCrossObservation_antitone U.tree s t (U.clock h)
      (U.clock_antitone h) r l hr hl) (Nat.le_succ i)) j le_rfl

theorem cavityGeneratedObservedRawCrossComponent_support
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h∈U.supportSet) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (U.clock h) U.tree s r)
    (hl : cavityGeneratedRawCrossCell (U.clock h) U.tree t l)
    (hk : cavityGeneratedRawCrossChartHolds U.tree s t k r l)
    (hs : r=nativeStreamingOriginLevel (U.clock h) (cavityGeneratedRawCrossOrigin U.tree s r))
    (ht : l=nativeStreamingOriginLevel (U.clock h) (cavityGeneratedRawCrossOrigin U.tree t l)) :
    cavityGeneratedRawCrossAppend h r l∈(cavityGeneratedObservedRawCrossComponent U s t k).supportSet := by
  let R := cavityGeneratedObservedRawCrossObservedComponent U s t
  let v := cavityGeneratedRawCrossObservationFirst U.tree s t k
  let w := cavityGeneratedRawCrossObservationSecond U.tree s t k
  let H := cavityGeneratedRawCrossAppend h r l
  have hR : H∈R.supportSet := cavityGeneratedObservedRawCrossObservedComponent_support U s t h hh r l hr hl
  have hclock : R.clock H=cavityGeneratedRawCrossObservationClock U.tree s t (U.clock h) r l := by
    change cavityGeneratedClippedClock (cavityGeneratedRawCrossComponentClock U s t H)=_
    rw [cavityGeneratedRawCrossComponentClock_append]
    funext j
    exact cavityGeneratedClippedClock_eq _ j
      (fun i _=>(cavityGeneratedRawCrossObservation_antitone U.tree s t (U.clock h)
        (U.clock_antitone h) r l hr hl) (Nat.le_succ i)) j le_rfl
  have hb : H (cavityGeneratedRawCrossFirstMark m)=R.clock H v.depth := by
    rw [hclock,cavityGeneratedRawCrossObservation_first_clock U.tree s t k (U.clock h) r l hk]
    simpa only [H,cavityGeneratedRawCrossFirstMark,cavityGeneratedRawCrossAppend,
      Fin.snoc_castSucc,Fin.snoc_last] using hs
  let A := cavityGeneratedObservedRawVertexGraftComponent R v (cavityGeneratedRawCrossFirstMark m) .single
  have hA : H∈A.supportSet := cavityGeneratedObservedRawVertexGraftComponent_support R v
    (cavityGeneratedRawCrossFirstMark m) .single H hR hb
  apply cavityGeneratedObservedRawVertexGraftComponent_support A
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w)
    (cavityGeneratedRawCrossSecondMark m) .single H hA
  change H (cavityGeneratedRawCrossSecondMark m)=R.clock H
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w).depth
  rw [finiteCascadeContinuationVertexEmbed_depth,hclock,
    cavityGeneratedRawCrossObservation_second_clock U.tree s t k (U.clock h) r l hk]
  simpa only [H,cavityGeneratedRawCrossSecondMark,cavityGeneratedRawCrossAppend,Fin.snoc_last] using ht

theorem cavityGeneratedObservedRawCrossComponent_leafCount
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (cavityGeneratedObservedRawCrossComponent U s t k).tree)=
      FiniteCascadeGenealogy.leafCount (asGenealogy U.tree)+2 := by
  let R := cavityGeneratedObservedRawCrossObservedComponent U s t
  let v := cavityGeneratedRawCrossObservationFirst U.tree s t k
  let w := cavityGeneratedRawCrossObservationSecond U.tree s t k
  let A := cavityGeneratedObservedRawVertexGraftComponent R v (cavityGeneratedRawCrossFirstMark m) .single
  change FiniteCascadeGenealogy.leafCount (asGenealogy (cavityGeneratedObservedRawVertexGraftComponent A
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w) (cavityGeneratedRawCrossSecondMark m) .single).tree)=_
  rw [cavityGeneratedObservedRawVertexGraftComponent_leafCount]
  dsimp only [A]
  rw [cavityGeneratedObservedRawVertexGraftComponent_leafCount]
  have hR := cavityGeneratedRawRefinementComponent_leafCount U
    (cavityGeneratedRawCrossSubdivision U.tree s t) (cavityGeneratedRawCrossComponentClock U s t)
    (measurable_cavityGeneratedRawCrossComponentClock U s t)
    (cavityGeneratedRawCrossComponentClock_terminal U s t)
    (cavityGeneratedRawCrossComponentClock_initial U s t) (fun i=>i.castSucc.castSucc)
  change FiniteCascadeGenealogy.leafCount (asGenealogy R.tree)+1+1=_
  rw [show FiniteCascadeGenealogy.leafCount (asGenealogy R.tree)=
    FiniteCascadeGenealogy.leafCount (asGenealogy U.tree) from hR]

end QuantitativeFollowup
