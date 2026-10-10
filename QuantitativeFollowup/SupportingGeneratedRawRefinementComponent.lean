module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import QuantitativeFollowup.SupportingGeneratedRawRefinementForkProvenance

@[expose] public section

/-! An actual observation subdivision inherits the exact ordered old
fork indices. Output validity follows from the old support, the genuine
refined clock, and the inherited coordinates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m M : ℕ}

def cavityGeneratedRawRefinementComponent (U : CavityGeneratedObservedRawComponent m)
    (d : ℕ → ℕ) (Q : CavityGeneratedHistory Paper.Overlap M → ℕ → Paper.Overlap)
    (hQ : ∀j, Measurable (fun H => Q H j))
    (hzero : ∀H, Q H 0 = 1)
    (hinitial : ∀H, Q H (observationRefinementDepth d U.depth) = 0)
    (τ : Fin m → Fin M) : CavityGeneratedObservedRawComponent M where
  depth := observationRefinementDepth d U.depth
  tree := observationRefineTree d U.tree
  rawClock := Q
  measurable_rawClock := hQ
  rawClock_terminal := hzero
  rawClock_initial := hinitial
  forkMark i := τ (U.forkMark (Fin.cast (cavityGeneratedRawRefinementForkCount d U.tree) i))

theorem cavityGeneratedRawRefinementComponent_leafCount
    (U : CavityGeneratedObservedRawComponent m)
    (d : ℕ → ℕ) (Q : CavityGeneratedHistory Paper.Overlap M → ℕ → Paper.Overlap)
    (hQ : ∀j, Measurable (fun H => Q H j))
    (hzero : ∀H, Q H 0 = 1)
    (hinitial : ∀H, Q H (observationRefinementDepth d U.depth) = 0)
    (τ : Fin m → Fin M) :
    FiniteCascadeGenealogy.leafCount
      (asGenealogy (cavityGeneratedRawRefinementComponent U d Q hQ hzero hinitial τ).tree) =
        FiniteCascadeGenealogy.leafCount (asGenealogy U.tree) :=
  leafCount_observationRefineTree d U.tree

theorem cavityGeneratedRawRefinementComponent_support
    (U : CavityGeneratedObservedRawComponent m)
    (d : ℕ → ℕ) (Q : CavityGeneratedHistory Paper.Overlap M → ℕ → Paper.Overlap)
    (hQ : ∀j, Measurable (fun H => Q H j))
    (hzero : ∀H, Q H 0 = 1)
    (hinitial : ∀H, Q H (observationRefinementDepth d U.depth) = 0)
    (τ : Fin m → Fin M) (h : CavityGeneratedHistory Paper.Overlap m)
    (H : CavityGeneratedHistory Paper.Overlap M) (hh : h ∈ U.supportSet)
    (hmono : Antitone (Q H))
    (hlevels : ∀j, Q H (observationRefinementDepth d j) = U.clock h j)
    (hcoord : ∀i, H (τ i) = h i) :
    H ∈ (cavityGeneratedRawRefinementComponent U d Q hQ hzero hinitial τ).supportSet := by
  constructor
  · intro j
    exact hmono (Nat.le_succ j)
  · intro i
    let k := Fin.cast (cavityGeneratedRawRefinementForkCount d U.tree) i
    have he := cavityGeneratedRawRefinementForkIndex_get d U.tree k
    simp only [k,Fin.cast_cast,Fin.cast_eq_self] at he
    change Q H ((cavityGeneratedOriginForkVertices (observationRefineTree d U.tree)).get i).depth =
      H (τ (U.forkMark k))
    rw [he,nativeStreamingRefinementVertexEmbed_depth,hlevels]
    rw [U.fork_clock_is_mark h hh k,hcoord]

end QuantitativeFollowup
