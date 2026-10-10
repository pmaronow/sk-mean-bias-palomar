module
public import QuantitativeFollowup.SupportingGeneratedRawRefinementComponent
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureGraftComponent
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureGeometry

@[expose] public section

/-! The raw future component uses two appended retained coordinates.
Its actual original source cell supplies output antitonicity and both new
fork labels; inactive charts still have a genuine tree with two new leaves. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedObservedRawFutureHistoryPrefix
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : CavityGeneratedHistory Paper.Overlap m :=
  fun i => H i.castSucc.castSucc

def cavityGeneratedObservedRawFutureFirstMark : Fin (m+2) := (Fin.last m).castSucc
def cavityGeneratedObservedRawFutureSecondMark : Fin (m+2) := Fin.last (m+1)

theorem measurable_cavityGeneratedObservedRawFutureHistoryPrefix :
    Measurable (cavityGeneratedObservedRawFutureHistoryPrefix (m:=m)) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply i.castSucc.castSucc)

def cavityGeneratedObservedRawFutureComponentClock (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℕ → Paper.Overlap :=
  cavityGeneratedObservedRawFutureClock (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H))
    U.tree γ j (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark)

theorem measurable_cavityGeneratedObservedRawFutureComponentClock
    (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth) (k : ℕ) :
    Measurable (fun H => cavityGeneratedObservedRawFutureComponentClock U γ j H k) := by
  have hq (i : ℕ) : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) i) :=
    (U.measurable_clock i).comp measurable_cavityGeneratedObservedRawFutureHistoryPrefix
  have hr : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      H cavityGeneratedObservedRawFutureFirstMark) := measurable_pi_apply _
  have hl : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      H cavityGeneratedObservedRawFutureSecondMark) := measurable_pi_apply _
  rcases γ with i | (i | u)
  · change Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      nativeStreamingEdgeSchedule (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H))
        j (H cavityGeneratedObservedRawFutureSecondMark) k)
    unfold nativeStreamingEdgeSchedule
    split_ifs <;> first | exact hq _ | exact hl
  · change Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      nativeStreamingPairObservationSchedule (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H))
        ((cavityGeneratedOriginEdges U.tree).get i).depth j
        (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark) k)
    unfold nativeStreamingPairObservationSchedule nativeStreamingPairObservationTimes
    split_ifs <;> first | exact hq _ | exact hr.max hl | exact hr.min hl | exact hr | exact hl
  · change Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      nativeStreamingEdgeSchedule (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H))
        j (H cavityGeneratedObservedRawFutureSecondMark) k)
    unfold nativeStreamingEdgeSchedule
    split_ifs <;> first | exact hq _ | exact hl

def cavityGeneratedObservedRawFutureObservedComponent
    (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth) :
    CavityGeneratedObservedRawComponent (m+2) :=
  cavityGeneratedRawRefinementComponent U (cavityGeneratedObservedRawFutureSubdivision U.tree γ j)
    (cavityGeneratedObservedRawFutureComponentClock U γ j)
    (measurable_cavityGeneratedObservedRawFutureComponentClock U γ j)
    (fun H => by
      have he := cavityGeneratedObservedRawFutureClock_refinement
        (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)) U.tree γ j
        (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark) 0
      exact he.trans (U.clock_terminal _))
    (fun H => (cavityGeneratedObservedRawFutureClock_refinement
      (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)) U.tree γ j
      (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark) U.depth).trans
        (U.clock_initial _))
    (fun i => i.castSucc.castSucc)

def cavityGeneratedObservedRawFutureComponent (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth) :
    CavityGeneratedObservedRawComponent (m+2) :=
  cavityGeneratedObservedRawFutureGraftComponent
    (cavityGeneratedObservedRawFutureObservedComponent U γ j)
    (cavityGeneratedObservedRawFutureAnchor U.tree γ j)
    (cavityGeneratedObservedRawFutureSplit U.tree γ j)
    cavityGeneratedObservedRawFutureFirstMark cavityGeneratedObservedRawFutureSecondMark

def cavityGeneratedObservedRawFutureComponentEvent (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth) :
    Set (CavityGeneratedHistory Paper.Overlap (m+2)) :=
  {H | cavityGeneratedObservedRawFutureHistoryPrefix H ∈ U.supportSet ∧
    cavityGeneratedObservedRawFutureSourceCell (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H))
      U.tree γ j (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark)}

theorem measurableSet_cavityGeneratedObservedRawFutureComponentEvent
    (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth) :
    MeasurableSet (cavityGeneratedObservedRawFutureComponentEvent U γ j) := by
  have hq (i : ℕ) : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) i) :=
    (U.measurable_clock i).comp measurable_cavityGeneratedObservedRawFutureHistoryPrefix
  have hr : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      H cavityGeneratedObservedRawFutureFirstMark) := measurable_pi_apply _
  have hl : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      H cavityGeneratedObservedRawFutureSecondMark) := measurable_pi_apply _
  have hqr (i : ℕ) := measurable_subtype_coe.comp (hq i)
  have hrr := measurable_subtype_coe.comp hr
  have hlr := measurable_subtype_coe.comp hl
  apply (U.measurableSet_supportSet.preimage
    measurable_cavityGeneratedObservedRawFutureHistoryPrefix).inter
  rcases γ with i | (i | u)
  · change MeasurableSet {H | H cavityGeneratedObservedRawFutureFirstMark =
        U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)
          ((cavityGeneratedOriginForkVertices U.tree).get i).depth ∧ True ∧
        ((U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) (j+1) : ℝ) <
          (H cavityGeneratedObservedRawFutureSecondMark : ℝ) ∧
        (H cavityGeneratedObservedRawFutureSecondMark : ℝ) ≤
          (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) j : ℝ)) ∧
        (H cavityGeneratedObservedRawFutureFirstMark : ℝ) <
          (H cavityGeneratedObservedRawFutureSecondMark : ℝ)}
    exact (measurableSet_eq_fun hr (hq _)).inter
      (MeasurableSet.univ.inter (((measurableSet_lt (hqr _) hlr).inter
        (measurableSet_le hlr (hqr _))).inter (measurableSet_lt hrr hlr)))
  · change MeasurableSet {H | H cavityGeneratedObservedRawFutureFirstMark =
        H cavityGeneratedObservedRawFutureFirstMark ∧
        ((U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)
          (((cavityGeneratedOriginEdges U.tree).get i).depth+1) : ℝ) <
            (H cavityGeneratedObservedRawFutureFirstMark : ℝ) ∧
          (H cavityGeneratedObservedRawFutureFirstMark : ℝ) ≤
            (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)
              ((cavityGeneratedOriginEdges U.tree).get i).depth : ℝ)) ∧
        ((U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) (j+1) : ℝ) <
          (H cavityGeneratedObservedRawFutureSecondMark : ℝ) ∧
          (H cavityGeneratedObservedRawFutureSecondMark : ℝ) ≤
            (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) j : ℝ)) ∧
        (H cavityGeneratedObservedRawFutureFirstMark : ℝ) <
          (H cavityGeneratedObservedRawFutureSecondMark : ℝ)}
    exact (measurableSet_eq_fun hr hr).inter
      (((measurableSet_lt (hqr _) hrr).inter (measurableSet_le hrr (hqr _))).inter
        (((measurableSet_lt (hqr _) hlr).inter (measurableSet_le hlr (hqr _))).inter
          (measurableSet_lt hrr hlr)))
  · change MeasurableSet {H | H cavityGeneratedObservedRawFutureFirstMark =
        U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) U.depth ∧ True ∧
        ((U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) (j+1) : ℝ) <
          (H cavityGeneratedObservedRawFutureSecondMark : ℝ) ∧
        (H cavityGeneratedObservedRawFutureSecondMark : ℝ) ≤
          (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) j : ℝ)) ∧
        (H cavityGeneratedObservedRawFutureFirstMark : ℝ) <
          (H cavityGeneratedObservedRawFutureSecondMark : ℝ)}
    exact (measurableSet_eq_fun hr (hq _)).inter
      (MeasurableSet.univ.inter (((measurableSet_lt (hqr _) hlr).inter
        (measurableSet_le hlr (hqr _))).inter (measurableSet_lt hrr hlr)))

theorem cavityGeneratedObservedRawFutureComponent_tree (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth) :
    (cavityGeneratedObservedRawFutureComponent U γ j).tree =
      cavityGeneratedObservedRawFutureTree U.tree γ j := rfl

theorem cavityGeneratedObservedRawFutureComponent_leafCount (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (cavityGeneratedObservedRawFutureComponent U γ j).tree) =
      FiniteCascadeGenealogy.leafCount (asGenealogy U.tree)+2 :=
  cavityGeneratedObservedRawFutureTree_leafCount U.tree γ j

theorem cavityGeneratedObservedRawFutureComponent_rawClock (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    (cavityGeneratedObservedRawFutureComponent U γ j).rawClock H =
      cavityGeneratedObservedRawFutureComponentClock U γ j H := rfl

theorem cavityGeneratedObservedRawFutureComponent_support (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (hH : H ∈ cavityGeneratedObservedRawFutureComponentEvent U γ j) :
    H ∈ (cavityGeneratedObservedRawFutureComponent U γ j).supportSet := by
  let h := cavityGeneratedObservedRawFutureHistoryPrefix H
  let q := U.clock h
  let r := H cavityGeneratedObservedRawFutureFirstMark
  let l := H cavityGeneratedObservedRawFutureSecondMark
  let V := cavityGeneratedObservedRawFutureObservedComponent U γ j
  have hmono := cavityGeneratedObservedRawFutureClock_antitone q (U.clock_antitone h)
    U.tree γ j r l hH.2
  have hV : H ∈ V.supportSet :=
    cavityGeneratedRawRefinementComponent_support U _ _ _ _ _ _ h H hH.1 hmono
      (cavityGeneratedObservedRawFutureClock_refinement q U.tree γ j r l) (fun _ => rfl)
  have hp := cavityGeneratedObservedRawFutureSplit_le_anchor q (U.clock_antitone h)
    U.tree γ j r l hH.2
  have hb : H cavityGeneratedObservedRawFutureFirstMark =
      V.clock H (cavityGeneratedObservedRawFutureAnchor U.tree γ j).depth := by
    rw [V.clock_eq_raw H hV.1 _ (FiniteCascadeRecordVertex.depth_le _)]
    exact (cavityGeneratedObservedRawFutureClock_anchor q U.tree γ j r l hH.2).symm
  have hc : H cavityGeneratedObservedRawFutureSecondMark =
      V.clock H (cavityGeneratedObservedRawFutureSplit U.tree γ j) := by
    rw [V.clock_eq_raw H hV.1 _ (hp.trans (FiniteCascadeRecordVertex.depth_le _))]
    exact (cavityGeneratedObservedRawFutureClock_split q U.tree γ j r l hH.2.2.2.2).symm
  exact cavityGeneratedObservedRawFutureGraftComponent_support V _ _ hp _ _ H hV hb hc

end QuantitativeFollowup
