module
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureComponent
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawSourceBudgets
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawLeafCounts

@[expose] public section

/-! A raw future family keeps the genuine selected original payload and
an independent free draw until the final double-snoc map. Its event uses
the original halfclosed cells and strict future clock. Support, exact
leaf count, and the normalized budget are consequences of this factory. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedObservedRawFuturePayloadChart {J : ℕ} (T : FiniteTerminalGenealogy J) :
    CavityGeneratedOriginSelection T → CavityGeneratedObservedRawOriginChart T
  | .inl i => .inl i
  | .inr (.inl z) => .inr (.inl z.1)
  | .inr (.inr u) => .inr (.inr u)

theorem measurable_cavityGeneratedObservedRawFuturePayloadChart {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    Measurable (cavityGeneratedObservedRawFuturePayloadChart T) := by
  apply measurable_fun_sum
  · exact measurable_inl
  · apply measurable_fun_sum
    · exact (measurable_inr.comp measurable_inl).comp measurable_fst
    · exact measurable_inr.comp measurable_inr

private theorem rawFutureChartSingleton {J : ℕ} (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) : MeasurableSet ({γ} : Set _) := by
  rcases γ with i | (i | u)
  · have hh : MeasurableSet (Sum.inl '' ({i} : Set (Fin
        (cavityGeneratedOriginForkVertices T).length)) : Set (CavityGeneratedObservedRawOriginChart T)) :=
      (measurableSet_singleton i).inl_image
    simpa only [Set.image_singleton] using hh
  · have hi : MeasurableSet (Sum.inl '' ({i} : Set (Fin
        (cavityGeneratedOriginEdges T).length)) : Set (Fin
        (cavityGeneratedOriginEdges T).length ⊕ Unit)) := (measurableSet_singleton i).inl_image
    have hh : MeasurableSet (Sum.inr '' (Sum.inl '' ({i} : Set (Fin
        (cavityGeneratedOriginEdges T).length))) : Set (CavityGeneratedObservedRawOriginChart T)) := hi.inr_image
    simpa only [Set.image_singleton] using hh
  · have hi : MeasurableSet (Sum.inr '' ({u} : Set Unit) : Set (Fin
        (cavityGeneratedOriginEdges T).length ⊕ Unit)) := (measurableSet_singleton u).inr_image
    have hh : MeasurableSet (Sum.inr '' (Sum.inr '' ({u} : Set Unit)) :
        Set (CavityGeneratedObservedRawOriginChart T)) := hi.inr_image
    simpa only [Set.image_singleton] using hh

def cavityGeneratedObservedRawFutureForest (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c)) : CavityGeneratedObservedRawForest (m+2) :=
  cavityGeneratedObservedRawForestReplaceComponent (W.reindex (fun i => i.castSucc.castSucc)) c
    (cavityGeneratedObservedRawFutureComponent (W.component c) γ j)

def cavityGeneratedObservedRawFutureAppend (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) :
    (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap → CavityGeneratedHistory Paper.Overlap (m+2) :=
  cavityGeneratedRawOriginFutureAppendedHistory (fun h => W.clock h c) (W.tree c)

theorem measurable_cavityGeneratedObservedRawFutureAppend
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    Measurable (cavityGeneratedObservedRawFutureAppend W c) :=
  measurable_cavityGeneratedRawOriginFutureAppendedHistory _ (W.measurable_clock c) (W.tree c)

theorem cavityGeneratedObservedRawFutureAppend_prefix
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) :
    cavityGeneratedObservedRawFutureHistoryPrefix (cavityGeneratedObservedRawFutureAppend W c z) = z.1.1 := by
  funext i
  simp only [cavityGeneratedObservedRawFutureHistoryPrefix,cavityGeneratedObservedRawFutureAppend,
    cavityGeneratedRawOriginFutureAppendedHistory,cavityGeneratedRawOriginAppendedHistory,Fin.snoc_castSucc]

def cavityGeneratedObservedRawFutureSourceEvent (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c)) :
    Set ((CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) :=
  {z | z.1.1 ∈ W.supportSet ∧ cavityGeneratedObservedRawFuturePayloadChart (W.tree c) z.1.2 = γ ∧
    cavityGeneratedObservedRawFutureAppend W c z ∈
      cavityGeneratedObservedRawFutureComponentEvent (W.component c) γ j}

theorem measurableSet_cavityGeneratedObservedRawFutureSourceEvent
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c)) :
    MeasurableSet (cavityGeneratedObservedRawFutureSourceEvent W c γ j) := by
  have hchart : MeasurableSet {z :
      (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap |
        cavityGeneratedObservedRawFuturePayloadChart (W.tree c) z.1.2 = γ} :=
    (rawFutureChartSingleton (W.tree c) γ).preimage
      ((measurable_cavityGeneratedObservedRawFuturePayloadChart (W.tree c)).comp measurable_fst.snd)
  exact (W.measurableSet_supportSet.preimage measurable_fst.fst).inter
    (hchart.inter ((measurableSet_cavityGeneratedObservedRawFutureComponentEvent (W.component c) γ j).preimage
      (measurable_cavityGeneratedObservedRawFutureAppend W c)))

theorem cavityGeneratedObservedRawFutureForest_leafCount
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c)) :
    (cavityGeneratedObservedRawFutureForest W c γ j).leafCount = W.leafCount + 2 := by
  have he := cavityGeneratedObservedRawForestReplaceComponent_leafCount
    (W.reindex (fun i => i.castSucc.castSucc)) c
    (cavityGeneratedObservedRawFutureComponent (W.component c) γ j)
  have hu := cavityGeneratedObservedRawFutureComponent_leafCount (W.component c) γ j
  change (cavityGeneratedObservedRawFutureForest W c γ j).leafCount + (W.component c).leafCount =
    W.leafCount + (cavityGeneratedObservedRawFutureComponent (W.component c) γ j).leafCount at he
  change (cavityGeneratedObservedRawFutureComponent (W.component c) γ j).leafCount =
    (W.component c).leafCount+2 at hu
  omega

theorem cavityGeneratedObservedRawFutureForest_support
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) (hz : z ∈ cavityGeneratedObservedRawFutureSourceEvent W c γ j) :
    cavityGeneratedObservedRawFutureAppend W c z ∈
      (cavityGeneratedObservedRawFutureForest W c γ j).supportSet := by
  classical
  change ∀i : Fin W.componentCount, cavityGeneratedObservedRawFutureAppend W c z ∈
    (Function.update (fun s => (W.component s).reindex (fun i => i.castSucc.castSucc)) c
      (cavityGeneratedObservedRawFutureComponent (W.component c) γ j) i).supportSet
  intro i
  by_cases hi : i=c
  · subst i
    rw [Function.update_self]
    exact cavityGeneratedObservedRawFutureComponent_support (W.component c) γ j _ hz.2.2
  · rw [Function.update_of_ne hi]
    have he := cavityGeneratedObservedRawFutureAppend_prefix W c z
    change cavityGeneratedObservedRawFutureHistoryPrefix
      (cavityGeneratedObservedRawFutureAppend W c z) ∈ (W.component i).supportSet
    rw [he]
    exact hz.1 i

def cavityGeneratedObservedRawFutureSourceMeasure (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+2)) :=
  cavityGeneratedRawOriginFutureSourceMeasure μ a (fun h => W.clock h c) (W.measurable_clock c)
    (W.tree c) M (cavityGeneratedObservedRawFutureSourceEvent W c γ j)

instance cavityGeneratedObservedRawFutureSourceMeasure_finite
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c)) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M] :
    IsFiniteMeasure (cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) := by
  unfold cavityGeneratedObservedRawFutureSourceMeasure cavityGeneratedRawOriginFutureSourceMeasure
  infer_instance

theorem cavityGeneratedObservedRawFutureSourceMeasure_support
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    ∀ᵐH ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M,
      H ∈ (cavityGeneratedObservedRawFutureForest W c γ j).supportSet := by
  apply (ae_map_iff (measurable_cavityGeneratedObservedRawFutureAppend W c).aemeasurable
    (cavityGeneratedObservedRawFutureForest W c γ j).measurableSet_supportSet).mpr
  exact (ae_restrict_mem (measurableSet_cavityGeneratedObservedRawFutureSourceEvent W c γ j)).mono
    (fun z hz => cavityGeneratedObservedRawFutureForest_support W c γ j z hz)

theorem cavityGeneratedObservedRawFutureSourceMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M] (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hs : ∀ᵐh ∂M, h ∈ W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*C) :=
  cavityGeneratedObservedRawOriginFutureSourceMeasure_budget μ a ha hμ W c M C hM hs _

end QuantitativeFollowup
