module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawDefinitions

@[expose] public section

/-! The raw source carrier has actual measurable clipped clocks and a
computed support set. Reindexing preserves its observed trees and fork
marks. Every arbitrary initial observation mesh satisfies this support. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m M C : ℕ}

namespace CavityGeneratedObservedRawComponent

theorem measurable_clock (U : CavityGeneratedObservedRawComponent m) (j : ℕ) :
    Measurable (fun h=>U.clock h j) := by
  induction j with
  | zero => exact U.measurable_rawClock 0
  | succ j ih => exact ih.min (U.measurable_rawClock (j+1))

theorem clock_antitone (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) : Antitone (U.clock h) :=
  antitone_nat_of_succ_le (fun j=>cavityGeneratedClippedClock_step_le _ j)

theorem clock_terminal (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) : U.clock h 0 = 1 := U.rawClock_terminal h

theorem clock_initial (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) : U.clock h U.depth = 0 := by
  cases hd : U.depth with
  | zero => simpa only [hd,clock,cavityGeneratedClippedClock] using U.rawClock_initial h
  | succ j =>
      change min (cavityGeneratedClippedClock (U.rawClock h) j) (U.rawClock h (j+1))=0
      rw [show U.rawClock h (j+1)=0 from by simpa only [hd] using U.rawClock_initial h]
      exact min_eq_right (show (0:ℝ)≤(cavityGeneratedClippedClock (U.rawClock h) j:ℝ)
        from (cavityGeneratedClippedClock (U.rawClock h) j).property.1)

theorem clock_eq_raw (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈U.orderSet)
    (j : ℕ) (hj : j≤U.depth) : U.clock h j=U.rawClock h j := by
  exact cavityGeneratedClippedClock_eq _ U.depth (fun d hd=>hh ⟨d,hd⟩) j hj

theorem measurableSet_orderSet (U : CavityGeneratedObservedRawComponent m) :
    MeasurableSet U.orderSet := by
  simp only [orderSet,setOf_forall]
  apply MeasurableSet.iInter
  intro j
  change MeasurableSet {h | (U.rawClock h (j+1):ℝ)≤(U.rawClock h j:ℝ)}
  exact measurableSet_le (measurable_subtype_coe.comp (U.measurable_rawClock _))
    (measurable_subtype_coe.comp (U.measurable_rawClock _))

theorem measurableSet_forkSet (U : CavityGeneratedObservedRawComponent m) :
    MeasurableSet U.forkSet := by
  simp only [forkSet,setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq_fun (U.measurable_rawClock _) (measurable_pi_apply (U.forkMark i))

theorem measurableSet_supportSet (U : CavityGeneratedObservedRawComponent m) :
    MeasurableSet U.supportSet := U.measurableSet_orderSet.inter U.measurableSet_forkSet

theorem fork_clock_is_mark (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈U.supportSet)
    (i : Fin (cavityGeneratedOriginForkVertices U.tree).length) :
    U.clock h ((cavityGeneratedOriginForkVertices U.tree).get i).depth = h (U.forkMark i) := by
  have hd : ((cavityGeneratedOriginForkVertices U.tree).get i).depth≤U.depth :=
    FiniteCascadeRecordVertex.depth_le _
  rw [U.clock_eq_raw h hh.1 _ hd]
  exact hh.2 i

def reindex (U : CavityGeneratedObservedRawComponent m) (τ : Fin m → Fin M) :
    CavityGeneratedObservedRawComponent M where
  depth := U.depth
  tree := U.tree
  rawClock H := U.rawClock (fun i=>H (τ i))
  measurable_rawClock j := (U.measurable_rawClock j).comp
    (measurable_pi_iff.mpr fun i=>measurable_pi_apply (τ i))
  rawClock_terminal H := U.rawClock_terminal _
  rawClock_initial H := U.rawClock_initial _
  forkMark i := τ (U.forkMark i)

theorem reindex_rawClock (U : CavityGeneratedObservedRawComponent m) (τ : Fin m → Fin M)
    (H : CavityGeneratedHistory Paper.Overlap M) :
    (U.reindex τ).rawClock H=U.rawClock (fun i=>H (τ i)) := rfl

theorem reindex_clock (U : CavityGeneratedObservedRawComponent m) (τ : Fin m → Fin M)
    (H : CavityGeneratedHistory Paper.Overlap M) :
    (U.reindex τ).clock H=U.clock (fun i=>H (τ i)) := rfl

theorem reindex_support (U : CavityGeneratedObservedRawComponent m) (τ : Fin m → Fin M)
    (H : CavityGeneratedHistory Paper.Overlap M) :
    H∈(U.reindex τ).supportSet ↔ (fun i=>H (τ i))∈U.supportSet := Iff.rfl

end CavityGeneratedObservedRawComponent

namespace CavityGeneratedObservedRawForest

theorem measurable_clock (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (j : ℕ) : Measurable (fun h=>W.clock h c j) :=
  (W.component c).measurable_clock j

theorem clock_antitone (W : CavityGeneratedObservedRawForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    Antitone (W.clock h c) := (W.component c).clock_antitone h

theorem clock_terminal (W : CavityGeneratedObservedRawForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    W.clock h c 0=1 := (W.component c).clock_terminal h

theorem clock_initial (W : CavityGeneratedObservedRawForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    W.clock h c (W.depth c)=0 := (W.component c).clock_initial h

theorem measurableSet_supportSet (W : CavityGeneratedObservedRawForest m) :
    MeasurableSet W.supportSet := by
  simp only [supportSet,setOf_forall]
  exact MeasurableSet.iInter (fun c=>(W.component c).measurableSet_supportSet)

def reindex (W : CavityGeneratedObservedRawForest m) (τ : Fin m → Fin M) :
    CavityGeneratedObservedRawForest M :=
  cavityGeneratedObservedRawForestOfComponents (fun c=>(W.component c).reindex τ)

theorem reindex_clock (W : CavityGeneratedObservedRawForest m) (τ : Fin m → Fin M)
    (H : CavityGeneratedHistory Paper.Overlap M) :
    (W.reindex τ).clock H=W.clock (fun i=>H (τ i)) := rfl

theorem reindex_support (W : CavityGeneratedObservedRawForest m) (τ : Fin m → Fin M)
    (H : CavityGeneratedHistory Paper.Overlap M) :
    H∈(W.reindex τ).supportSet ↔ (fun i=>H (τ i))∈W.supportSet := Iff.rfl

theorem reindex_leafCount (W : CavityGeneratedObservedRawForest m) (τ : Fin m → Fin M) :
    (W.reindex τ).leafCount=W.leafCount := rfl

end CavityGeneratedObservedRawForest

theorem cavityGeneratedObservedRawInitialForest_supportSet
    (S : CavityGeneratedObservedRawInitialForest C) :
    (cavityGeneratedObservedRawInitialForest S).supportSet=univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro h c
  constructor
  · intro j
    exact S.antitone_clock (h 0) c (Nat.le_succ j)
  · intro i
    have hd : ((cavityGeneratedOriginForkVertices (S.tree c)).get i).depth∈
        printedGeneratedOriginForkDepths (S.tree c) := by
      rw [←cavityGeneratedOriginForkVertices_depths]
      exact List.mem_map.mpr ⟨_,List.get_mem _ _,rfl⟩
    exact printedGeneratedInitialForkDepths_at (S.clock (h 0) c) (h 0) (S.tree c)
      (S.forks_at (h 0) c) _ hd

end QuantitativeFollowup
