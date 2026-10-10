module
public import QuantitativeFollowup.SupportingGeneratedRawForkProvenance
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import QuantitativeFollowup.SupportingGeneratedOriginComponentCharts

@[expose] public section

/-! A genuine vertex continuation on the raw observed carrier retains all
unary clock functions. Its old fork labels are inherited through computed
fork provenance; the actual new forks use the selected retained mark. The
output support is derived from the input support and the selected clock. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

private theorem rawLinearForks_empty (J : ℕ) :
    cavityGeneratedOriginForkVertices (observationLinearTree J) = [] := by
  induction J with
  | zero => rfl
  | succ J ih =>
      change (cavityGeneratedOriginForkVertices (observationLinearTree J)).map FiniteCascadeRecordVertex.child=[]
      rw [ih]
      rfl

theorem cavityGeneratedRawKindFork_depth
    (k : NativeStreamingGeneratedVertexKind) (J : ℕ)
    (v : FiniteCascadeRecordVertex (k.continuation J))
    (hv : v∈cavityGeneratedOriginForkVertices (k.continuation J)) : v.depth=J := by
  cases k with
  | single =>
      change v∈cavityGeneratedOriginForkVertices (observationLinearTree J) at hv
      rw [rawLinearForks_empty] at hv
      cases hv
  | current =>
      change v∈cavityGeneratedOriginForkVertices (.fork (observationLinearTree J) (observationLinearTree J)) at hv
      simp only [cavityGeneratedOriginForkVertices,rawLinearForks_empty,List.map_nil,List.nil_append,
        List.mem_singleton] at hv
      subst v
      rfl

def cavityGeneratedObservedRawVertexGraftComponent
    (U : CavityGeneratedObservedRawComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (b : Fin m) (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedObservedRawComponent m where
  depth := U.depth
  tree := finiteCascadeContinuationGraft k.continuation v
  rawClock := U.rawClock
  measurable_rawClock := U.measurable_rawClock
  rawClock_terminal := U.rawClock_terminal
  rawClock_initial := U.rawClock_initial
  forkMark i := match cavityGeneratedRawGraftForkRoute k.continuation v i with
    | .inl j => U.forkMark j
    | .inr (.inl _) => b
    | .inr (.inr _) => b

theorem cavityGeneratedObservedRawVertexGraftComponent_clock
    (U : CavityGeneratedObservedRawComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (b : Fin m) (k : NativeStreamingGeneratedVertexKind)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (cavityGeneratedObservedRawVertexGraftComponent U v b k).clock h=U.clock h := rfl

/-- The selected physical-clock equality alone pins the new forks to the retained mark. -/
theorem cavityGeneratedObservedRawVertexGraftComponent_support
    (U : CavityGeneratedObservedRawComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (b : Fin m) (k : NativeStreamingGeneratedVertexKind)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈U.supportSet)
    (hb : h b=U.clock h v.depth) :
    h∈(cavityGeneratedObservedRawVertexGraftComponent U v b k).supportSet := by
  constructor
  · exact hh.1
  · intro i
    have hd := cavityGeneratedRawGraftForkRoute_depth k.continuation v i
    cases hr : cavityGeneratedRawGraftForkRoute k.continuation v i with
    | inl j =>
        simp only [hr] at hd
        change U.rawClock h
          ((cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft k.continuation v)).get i).depth =
          h (match cavityGeneratedRawGraftForkRoute k.continuation v i with
            | .inl j => U.forkMark j
            | .inr (.inl _) => b
            | .inr (.inr _) => b)
        rw [hr,hd]
        exact hh.2 j
    | inr r => cases r with
      | inl j =>
          simp only [hr] at hd
          have hnew := cavityGeneratedRawKindFork_depth k v.depth
            ((cavityGeneratedOriginForkVertices (k.continuation v.depth)).get j) (List.get_mem _ j)
          change U.rawClock h
            ((cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft k.continuation v)).get i).depth =
            h (match cavityGeneratedRawGraftForkRoute k.continuation v i with
              | .inl j => U.forkMark j
              | .inr (.inl _) => b
              | .inr (.inr _) => b)
          rw [hr,hd,hnew,←U.clock_eq_raw h hh.1 v.depth v.depth_le]
          exact hb.symm
      | inr u =>
          simp only [hr] at hd
          change U.rawClock h
            ((cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft k.continuation v)).get i).depth =
            h (match cavityGeneratedRawGraftForkRoute k.continuation v i with
              | .inl j => U.forkMark j
              | .inr (.inl _) => b
              | .inr (.inr _) => b)
          rw [hr,hd,←U.clock_eq_raw h hh.1 v.depth v.depth_le]
          exact hb.symm

theorem cavityGeneratedObservedRawVertexGraftComponent_leafCount
    (U : CavityGeneratedObservedRawComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (b : Fin m) (k : NativeStreamingGeneratedVertexKind) :
    FiniteCascadeGenealogy.leafCount
      (asGenealogy (cavityGeneratedObservedRawVertexGraftComponent U v b k).tree) =
      FiniteCascadeGenealogy.leafCount (asGenealogy U.tree)+k.newLeafCount := by
  change FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeContinuationGraft k.continuation v)) = _
  rw [finiteCascadeContinuationGraft_leafCount,printedGeneratedContinuation_leafCount]

end QuantitativeFollowup
