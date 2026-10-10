module
public import QuantitativeFollowup.SupportingGeneratedRawForkProvenance
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import FourPapersCommon.FiniteCascadeFutureVertexGraft

@[expose] public section

/-! The shared future continuation has one genuine fresh fork at its
actual split and one added attachment fork. Both retained mark labels
are computed through the actual graft fork provenance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

private theorem rawFutureLinearForks_empty (J : ℕ) :
    cavityGeneratedOriginForkVertices (observationLinearTree J) = [] := by
  induction J with
  | zero => rfl
  | succ J ih =>
      change (cavityGeneratedOriginForkVertices (observationLinearTree J)).map
        FiniteCascadeRecordVertex.child = []
      rw [ih]
      rfl

theorem cavityGeneratedObservedRawPairTreeFork_depth {J : ℕ} (P : ObservationPairTree J)
    (v : FiniteCascadeRecordVertex P.tree)
    (hv : v ∈ cavityGeneratedOriginForkVertices P.tree) : v.depth = P.splitLevel := by
  induction P with
  | advance P ih =>
      simp only [ObservationPairTree.tree,cavityGeneratedOriginForkVertices,List.mem_map] at hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact ih w hw
  | split d reverse =>
      cases reverse <;>
        simp only [ObservationPairTree.tree,cavityGeneratedOriginForkVertices,
          rawFutureLinearForks_empty,List.map_nil,List.nil_append,List.mem_singleton] at hv <;>
        subst v <;> rfl

def cavityGeneratedObservedRawFutureGraftComponent (U : CavityGeneratedObservedRawComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (p : ℕ) (b c : Fin m) :
    CavityGeneratedObservedRawComponent m where
  depth := U.depth
  tree := finiteCascadeFutureVertexGraft v p
  rawClock := U.rawClock
  measurable_rawClock := U.measurable_rawClock
  rawClock_terminal := U.rawClock_terminal
  rawClock_initial := U.rawClock_initial
  forkMark i := match cavityGeneratedRawGraftForkRoute
      (fun j => (finiteCascadeFuturePairTree p j).tree) v i with
    | .inl j => U.forkMark j
    | .inr (.inl _) => c
    | .inr (.inr _) => b

theorem cavityGeneratedObservedRawFutureGraftComponent_clock
    (U : CavityGeneratedObservedRawComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (p : ℕ) (b c : Fin m) (h : CavityGeneratedHistory Paper.Overlap m) :
    (cavityGeneratedObservedRawFutureGraftComponent U v p b c).clock h = U.clock h := rfl

theorem cavityGeneratedObservedRawFutureGraftComponent_leafCount
    (U : CavityGeneratedObservedRawComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (p : ℕ) (b c : Fin m) :
    FiniteCascadeGenealogy.leafCount
      (asGenealogy (cavityGeneratedObservedRawFutureGraftComponent U v p b c).tree) =
      FiniteCascadeGenealogy.leafCount (asGenealogy U.tree) + 2 :=
  finiteCascadeFutureVertexGraft_leafCount v p

theorem cavityGeneratedObservedRawFutureGraftComponent_support
    (U : CavityGeneratedObservedRawComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (p : ℕ) (hp : p ≤ v.depth) (b c : Fin m)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h ∈ U.supportSet)
    (hb : h b = U.clock h v.depth) (hc : h c = U.clock h p) :
    h ∈ (cavityGeneratedObservedRawFutureGraftComponent U v p b c).supportSet := by
  constructor
  · exact hh.1
  · change ∀i : Fin (cavityGeneratedOriginForkVertices
        (finiteCascadeContinuationGraft (fun j => (finiteCascadeFuturePairTree p j).tree) v)).length,
      U.rawClock h ((cavityGeneratedOriginForkVertices
        (finiteCascadeContinuationGraft (fun j => (finiteCascadeFuturePairTree p j).tree) v)).get i).depth =
        h (match cavityGeneratedRawGraftForkRoute (fun j => (finiteCascadeFuturePairTree p j).tree) v i with
        | .inl j => U.forkMark j
        | .inr (.inl _) => c
        | .inr (.inr _) => b)
    intro i
    have hd := cavityGeneratedRawGraftForkRoute_depth (fun j => (finiteCascadeFuturePairTree p j).tree) v i
    cases hr : cavityGeneratedRawGraftForkRoute (fun j => (finiteCascadeFuturePairTree p j).tree) v i with
    | inl j =>
        simp only [hr] at hd
        rw [hd]
        exact hh.2 j
    | inr r => cases r with
      | inl j =>
          simp only [hr] at hd
          have hnew := cavityGeneratedObservedRawPairTreeFork_depth (finiteCascadeFuturePairTree p v.depth)
            ((cavityGeneratedOriginForkVertices (finiteCascadeFuturePairTree p v.depth).tree).get j)
              (List.get_mem _ j)
          rw [finiteCascadeFuturePairTree_split p v.depth hp] at hnew
          rw [hd,hnew,←U.clock_eq_raw h hh.1 p (hp.trans v.depth_le)]
          exact hc.symm
      | inr u =>
          simp only [hr] at hd
          rw [hd,←U.clock_eq_raw h hh.1 v.depth v.depth_le]
          exact hb.symm

end QuantitativeFollowup
