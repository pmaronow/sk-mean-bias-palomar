module
public import QuantitativeFollowup.FollowupCavityGeneratedInitialForest
public import QuantitativeFollowup.FollowupCavityGeneratedForestProducts

@[expose] public section

/-! Concrete independent components of a generated forest. A normalizer
attachment adds an actual sibling genealogy, with its own native tilted
root. All components retain fixed endpoint labels and genuine branch
construction witnesses. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
variable {m n C : ℕ}

structure CavityGeneratedConstructedComponent (m : ℕ) where
  depth : ℕ
  tree : FiniteTerminalGenealogy depth
  label : Fin (depth+1)→CavityGeneratedClockLabel m
  terminal_label : label 0=.terminal
  initial_label : label (Fin.last depth)=.initial
  construction : CavityGeneratedGenealogyConstruction
    (cavityGeneratedFiniteClockLabels label) tree

def CavityGeneratedConstructedForest.component
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    CavityGeneratedConstructedComponent m where
  depth := W.depth c
  tree := W.tree c
  label := W.label c
  terminal_label := W.terminal_label c
  initial_label := W.initial_label c
  construction := W.construction c

def cavityGeneratedForestOfComponents
    (F : Fin C→CavityGeneratedConstructedComponent m) :
    CavityGeneratedConstructedForest m where
  componentCount := C
  depth := fun c=>(F c).depth
  tree := fun c=>(F c).tree
  label := fun c=>(F c).label
  terminal_label := fun c=>(F c).terminal_label
  initial_label := fun c=>(F c).initial_label
  construction := fun c=>(F c).construction

theorem cavityGeneratedForestOfComponents_component
    (F : Fin C→CavityGeneratedConstructedComponent m) (c : Fin C) :
    (cavityGeneratedForestOfComponents F).component c=F c := rfl

def CavityGeneratedConstructedForest.appendComponent
    (W : CavityGeneratedConstructedForest m)
    (U : CavityGeneratedConstructedComponent m) : CavityGeneratedConstructedForest m :=
  cavityGeneratedForestOfComponents (Fin.snoc W.component U)

theorem CavityGeneratedConstructedForest.appendComponent_count
    (W : CavityGeneratedConstructedForest m)
    (U : CavityGeneratedConstructedComponent m) :
    (W.appendComponent U).componentCount=W.componentCount+1 := rfl

theorem CavityGeneratedConstructedForest.appendComponent_old
    (W : CavityGeneratedConstructedForest m)
    (U : CavityGeneratedConstructedComponent m) (c : Fin W.componentCount) :
    (W.appendComponent U).component c.castSucc=W.component c := by
  change (cavityGeneratedForestOfComponents (Fin.snoc W.component U)).component c.castSucc=_
  rw [cavityGeneratedForestOfComponents_component,Fin.snoc_castSucc]

theorem CavityGeneratedConstructedForest.appendComponent_new
    (W : CavityGeneratedConstructedForest m)
    (U : CavityGeneratedConstructedComponent m) :
    (W.appendComponent U).component (Fin.last W.componentCount)=U := by
  change (cavityGeneratedForestOfComponents (Fin.snoc W.component U)).component (Fin.last W.componentCount)=_
  rw [cavityGeneratedForestOfComponents_component,Fin.snoc_last]

def cavityGeneratedSiblingComponentLabels (i : Fin m)
    (j : Fin 3) : CavityGeneratedClockLabel m :=
  if j.val=0 then .terminal else if j.val=1 then .mark i else .initial

def cavityGeneratedSiblingComponent (i : Fin m) (S : CavityGeneratedSiblingShape) :
    CavityGeneratedConstructedComponent m where
  depth := 2
  tree := .advance S.tree
  label := cavityGeneratedSiblingComponentLabels i
  terminal_label := rfl
  initial_label := rfl
  construction := by
    apply CavityGeneratedGenealogyConstruction.advance
    induction S with
    | single => exact .advance (.linear 0)
    | fork S T ihS ihT => exact .fork i rfl ihS ihT

def cavityGeneratedInitialSiblingForest (S : Fin C→CavityGeneratedSiblingShape) :
    CavityGeneratedConstructedForest 1 :=
  cavityGeneratedForestOfComponents (fun c=>cavityGeneratedSiblingComponent 0 (S c))

theorem cavityGeneratedInitialSiblingForest_orderSet_eq_univ
    (S : Fin C→CavityGeneratedSiblingShape) :
    (cavityGeneratedInitialSiblingForest S).clockTemplate.orderSet=univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro h c j
  fin_cases j
  · change h 0≤(1:Paper.Overlap)
    exact (h 0).property.2
  · change (0:Paper.Overlap)≤h 0
    exact (h 0).property.1

end QuantitativeFollowup
