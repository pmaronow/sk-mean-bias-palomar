module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedSourceThreeDefects
public import QuantitativeFollowup.SupportingGeneratedInitialOriginClockBudget

@[expose] public section

/-! An observed source forest retains its actual unary clock functions.
Only genuine binary forks carry retained mark indices. Validity is a
computed measurable support set, not an assumed output-order field. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n d C : ℕ}

structure CavityGeneratedObservedRawComponent (m : ℕ) where
  depth : ℕ
  tree : FiniteTerminalGenealogy depth
  rawClock : CavityGeneratedHistory Paper.Overlap m → ℕ → Paper.Overlap
  measurable_rawClock : ∀j, Measurable (fun h=>rawClock h j)
  rawClock_terminal : ∀h, rawClock h 0 = 1
  rawClock_initial : ∀h, rawClock h depth = 0
  forkMark : Fin (cavityGeneratedOriginForkVertices tree).length → Fin m

namespace CavityGeneratedObservedRawComponent

def clock (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℕ → Paper.Overlap :=
  cavityGeneratedClippedClock (U.rawClock h)

def orderSet (U : CavityGeneratedObservedRawComponent m) :
    Set (CavityGeneratedHistory Paper.Overlap m) :=
  {h | ∀j : Fin U.depth, U.rawClock h (j+1) ≤ U.rawClock h j}

def forkSet (U : CavityGeneratedObservedRawComponent m) :
    Set (CavityGeneratedHistory Paper.Overlap m) :=
  {h | ∀i : Fin (cavityGeneratedOriginForkVertices U.tree).length,
    U.rawClock h ((cavityGeneratedOriginForkVertices U.tree).get i).depth = h (U.forkMark i)}

def supportSet (U : CavityGeneratedObservedRawComponent m) :
    Set (CavityGeneratedHistory Paper.Overlap m) := U.orderSet ∩ U.forkSet

end CavityGeneratedObservedRawComponent

structure CavityGeneratedObservedRawForest (m : ℕ) where
  componentCount : ℕ
  component : Fin componentCount → CavityGeneratedObservedRawComponent m

namespace CavityGeneratedObservedRawForest

def depth (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) : ℕ :=
  (W.component c).depth

def tree (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    FiniteTerminalGenealogy (W.depth c) := (W.component c).tree

def rawClock (W : CavityGeneratedObservedRawForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) : ℕ → Paper.Overlap :=
  (W.component c).rawClock h

def clock (W : CavityGeneratedObservedRawForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) : ℕ → Paper.Overlap :=
  (W.component c).clock h

def supportSet (W : CavityGeneratedObservedRawForest m) :
    Set (CavityGeneratedHistory Paper.Overlap m) :=
  {h | ∀c : Fin W.componentCount, h∈(W.component c).supportSet}

def leafCount (W : CavityGeneratedObservedRawForest m) : ℕ :=
  ∑c : Fin W.componentCount, FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c))

end CavityGeneratedObservedRawForest

def cavityGeneratedObservedRawForestOfComponents
    (F : Fin C → CavityGeneratedObservedRawComponent m) : CavityGeneratedObservedRawForest m :=
  ⟨C,F⟩

def cavityGeneratedObservedRawForestReplaceComponent
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (U : CavityGeneratedObservedRawComponent m) : CavityGeneratedObservedRawForest m := by
  classical
  exact cavityGeneratedObservedRawForestOfComponents (Function.update W.component c U)

def cavityGeneratedObservedRawForestAppendComponent
    (W : CavityGeneratedObservedRawForest m) (U : CavityGeneratedObservedRawComponent m) :
    CavityGeneratedObservedRawForest m :=
  cavityGeneratedObservedRawForestOfComponents (Fin.snoc W.component U)

abbrev CavityGeneratedObservedRawOriginChart {J : ℕ} (T : FiniteTerminalGenealogy J) :=
  Fin (cavityGeneratedOriginForkVertices T).length ⊕
    (Fin (cavityGeneratedOriginEdges T).length ⊕ Unit)

structure CavityGeneratedObservedRawPair (W : CavityGeneratedObservedRawForest m) where
  component : Fin W.componentCount
  first : ObservationLeaf (W.tree component)
  second : ObservationLeaf (W.tree component)

def cavityGeneratedObservedRawPairDefect (W : CavityGeneratedObservedRawForest m)
    (t : CavityGeneratedObservedRawPair W) (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) : ℝ :=
  cavitySpinOverlapDefect n
    (W.clock h t.component (observationCommonLevel (W.tree t.component) t.first t.second))
    (observationTerminalSpin (W.tree t.component) t.first (σ t.component))
    (observationTerminalSpin (W.tree t.component) t.second (σ t.component))

structure CavityGeneratedObservedRawTaggedTest (n : ℕ) (W : CavityGeneratedObservedRawForest m)
    (d : ℕ) where
  base : CavityGeneratedHistory Paper.Overlap m ×
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ
  pairs : Fin d → CavityGeneratedObservedRawPair W

def cavityGeneratedObservedRawTaggedValue (W : CavityGeneratedObservedRawForest m)
    (A : CavityGeneratedObservedRawTaggedTest n W d)
    (z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) : ℝ :=
  A.base z * ∏i : Fin d, cavityGeneratedObservedRawPairDefect W (A.pairs i) z.1 z.2

structure CavityGeneratedObservedRawInitialForest (C : ℕ) where
  depth : Fin C → ℕ
  tree : (c : Fin C) → FiniteTerminalGenealogy (depth c)
  clock : Paper.Overlap → Fin C → ℕ → Paper.Overlap
  measurable_clock : ∀c j, Measurable (fun p=>clock p c j)
  antitone_clock : ∀p c, Antitone (clock p c)
  terminal_clock : ∀p c, clock p c 0 = 1
  initial_clock : ∀p c, clock p c (depth c) = 0
  forks_at : ∀p c, printedGeneratedInitialForksAt (clock p c) p (tree c)

def cavityGeneratedObservedRawInitialComponent
    (S : CavityGeneratedObservedRawInitialForest C) (c : Fin C) :
    CavityGeneratedObservedRawComponent 1 where
  depth := S.depth c
  tree := S.tree c
  rawClock h := S.clock (h 0) c
  measurable_rawClock j := (S.measurable_clock c j).comp (measurable_pi_apply 0)
  rawClock_terminal h := S.terminal_clock (h 0) c
  rawClock_initial h := S.initial_clock (h 0) c
  forkMark _ := 0

def cavityGeneratedObservedRawInitialForest
    (S : CavityGeneratedObservedRawInitialForest C) : CavityGeneratedObservedRawForest 1 :=
  cavityGeneratedObservedRawForestOfComponents (cavityGeneratedObservedRawInitialComponent S)

def cavityGeneratedObservedRawInitialTaggedTest
    (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ) :
    CavityGeneratedObservedRawTaggedTest n (cavityGeneratedObservedRawInitialForest S) 0 :=
  ⟨F,Fin.elim0⟩

end QuantitativeFollowup
