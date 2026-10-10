module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import QuantitativeFollowup.FollowupCavityGeneratedNormalizerFamily

@[expose] public section

/-! The independent sixth raw source adds its genuine binary tree while
retaining every old observed component and every old mark coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedObservedRawNormalizerComponent : CavityGeneratedObservedRawComponent (m+1) where
  depth := 2
  tree := anisotropicBinaryObservationTree
  rawClock H := anisotropicBinaryObservationSchedule (H (Fin.last m))
  measurable_rawClock j := by
    cases j with
    | zero => exact measurable_const
    | succ j => cases j with
      | zero => exact measurable_pi_apply (Fin.last m)
      | succ j => exact measurable_const
  rawClock_terminal _ := rfl
  rawClock_initial _ := rfl
  forkMark _ := Fin.last m

def cavityGeneratedObservedRawNormalizerForest (W : CavityGeneratedObservedRawForest m) :
    CavityGeneratedObservedRawForest (m+1) :=
  cavityGeneratedObservedRawForestOfComponents
    (Fin.snoc (fun c=>(W.component c).reindex Fin.castSucc)
      cavityGeneratedObservedRawNormalizerComponent)

theorem cavityGeneratedObservedRawNormalizerForest_old_component
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    (cavityGeneratedObservedRawNormalizerForest W).component c.castSucc =
      (W.component c).reindex Fin.castSucc := by
  simp only [cavityGeneratedObservedRawNormalizerForest,
    cavityGeneratedObservedRawForestOfComponents,Fin.snoc_castSucc]

theorem cavityGeneratedObservedRawNormalizerForest_new_component
    (W : CavityGeneratedObservedRawForest m) :
    (cavityGeneratedObservedRawNormalizerForest W).component (Fin.last W.componentCount) =
      cavityGeneratedObservedRawNormalizerComponent := by
  simp only [cavityGeneratedObservedRawNormalizerForest,
    cavityGeneratedObservedRawForestOfComponents,Fin.snoc_last]

theorem cavityGeneratedObservedRawNormalizerComponent_clock
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    (cavityGeneratedObservedRawNormalizerComponent (m:=m)).clock H =
      anisotropicBinaryObservationSchedule (H (Fin.last m)) :=
  printedGeneratedClippedClock_of_antitone _ (printedGeneratedBinarySchedule_antitone _)

theorem cavityGeneratedObservedRawNormalizerComponent_support
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    H∈(cavityGeneratedObservedRawNormalizerComponent (m:=m)).supportSet := by
  constructor
  · intro j
    exact printedGeneratedBinarySchedule_antitone (H (Fin.last m)) (Nat.le_succ j)
  · intro i
    fin_cases i
    rfl

theorem cavityGeneratedObservedRawNormalizerForest_leafCount
    (W : CavityGeneratedObservedRawForest m) :
    (cavityGeneratedObservedRawNormalizerForest W).leafCount = W.leafCount+2 := by
  unfold CavityGeneratedObservedRawForest.leafCount
  change (∑c : Fin (W.componentCount+1),
    FiniteCascadeGenealogy.leafCount
      (asGenealogy ((cavityGeneratedObservedRawNormalizerForest W).tree c))) = _
  rw [Fin.sum_univ_castSucc]
  have hc (c : Fin W.componentCount) :
      FiniteCascadeGenealogy.leafCount (asGenealogy
        ((cavityGeneratedObservedRawNormalizerForest W).tree c.castSucc)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) :=
    congrArg (fun U : CavityGeneratedObservedRawComponent (m+1)=>
      FiniteCascadeGenealogy.leafCount (asGenealogy U.tree))
      (cavityGeneratedObservedRawNormalizerForest_old_component W c)
  have hl : FiniteCascadeGenealogy.leafCount (asGenealogy
      ((cavityGeneratedObservedRawNormalizerForest W).tree (Fin.last W.componentCount))) = 2 :=
    congrArg (fun U : CavityGeneratedObservedRawComponent (m+1)=>
      FiniteCascadeGenealogy.leafCount (asGenealogy U.tree))
      (cavityGeneratedObservedRawNormalizerForest_new_component W)
  simp only [hc,hl]

theorem cavityGeneratedObservedRawNormalizerForest_componentCount
    (W : CavityGeneratedObservedRawForest m) :
    (cavityGeneratedObservedRawNormalizerForest W).componentCount=W.componentCount+1 := rfl

theorem cavityGeneratedObservedRawNormalizerForest_snoc_support
    (W : CavityGeneratedObservedRawForest m) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h∈W.supportSet) :
    Fin.snoc h r∈(cavityGeneratedObservedRawNormalizerForest W).supportSet := by
  intro c
  cases c using Fin.lastCases with
  | last =>
      rw [cavityGeneratedObservedRawNormalizerForest_new_component]
      exact cavityGeneratedObservedRawNormalizerComponent_support _
  | cast c =>
      rw [cavityGeneratedObservedRawNormalizerForest_old_component,
        CavityGeneratedObservedRawComponent.reindex_support]
      have he : Fin.snoc h r ∘ Fin.castSucc=h := by
        funext i
        simp only [Function.comp_apply,Fin.snoc_castSucc]
      change (Fin.snoc h r ∘ Fin.castSucc)∈(W.component c).supportSet
      rw [he]
      exact hh c

theorem cavityGeneratedObservedRawNormalizerForest_support_ae
    (a : ℝ) (ha : a≤1) (ν : Measure Paper.Overlap) [SFinite ν]
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (W : CavityGeneratedObservedRawForest m) (hM : ∀ᵐh ∂M,h∈W.supportSet) :
    ∀ᵐH ∂cavityGeneratedNormalizerFamilyMeasure a ν M,
      H∈(cavityGeneratedObservedRawNormalizerForest W).supportSet := by
  have hs := (cavityGeneratedObservedRawNormalizerForest W).measurableSet_supportSet
  have hp : ∀ᵐz ∂M.prod ν,cavityGeneratedHistoryAppend z∈
      (cavityGeneratedObservedRawNormalizerForest W).supportSet := by
    apply (Measure.ae_prod_iff_ae_ae (hs.preimage cavityGeneratedHistoryAppend_measurable)).mpr
    exact hM.mono fun h hh=>.of_forall fun r=>cavityGeneratedObservedRawNormalizerForest_snoc_support W h r hh
  have hmap := (ae_map_iff cavityGeneratedHistoryAppend_measurable.aemeasurable hs).mpr hp
  exact hmap.filter_mono (ae_mono (cavityGeneratedNormalizerFamilyMeasure_le a ha ν M))

theorem cavityGeneratedObservedRawNormalizerForest_budget
    (a : ℝ) (ha : a≤1) (ν : Measure Paper.Overlap) [SFinite ν] (hν : ν univ≤1)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks C) :
    cavityGeneratedMarkBudget ν (cavityGeneratedNormalizerFamilyMeasure a ν M)
      cavityGeneratedHistoryMarks C :=
  cavityGeneratedNormalizerFamilyMeasure_budget a ha ν hν M C hM

end QuantitativeFollowup
