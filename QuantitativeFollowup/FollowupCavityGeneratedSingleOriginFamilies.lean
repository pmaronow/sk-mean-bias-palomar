module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionKernel
public import QuantitativeFollowup.SupportingGeneratedOriginComponentCharts
public import FourPapersCommon.FiniteMeasureChartPartition
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponentReplacementRetained

@[expose] public section

/-! A single/current attachment partitions the genuine selected payload.
Every chart uses the same original history, and the new forest is the
actual component graft with all untouched components reindexed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

instance cavityGeneratedOriginChart_measurableSpace (U : CavityGeneratedConstructedComponent m) :
    MeasurableSpace (PrintedGeneratedOriginChart U) :=
  inferInstanceAs (MeasurableSpace (Fin (cavityGeneratedOriginForkVertices U.tree).length ⊕
    (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)))

instance cavityGeneratedOriginChart_fintype (U : CavityGeneratedConstructedComponent m) :
    Fintype (PrintedGeneratedOriginChart U) :=
  inferInstanceAs (Fintype (Fin (cavityGeneratedOriginForkVertices U.tree).length ⊕
    (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)))

def cavityGeneratedOriginPayloadChart (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedOriginSelection U.tree → PrintedGeneratedOriginChart U
  | .inl i => .inl i
  | .inr (.inl z) => .inr (.inl z.1)
  | .inr (.inr u) => .inr (.inr u)

theorem measurable_cavityGeneratedOriginPayloadChart
    (U : CavityGeneratedConstructedComponent m) :
    Measurable (cavityGeneratedOriginPayloadChart U) := by
  apply measurable_fun_sum
  · exact measurable_inl
  · apply measurable_fun_sum
    · exact (measurable_inr.comp measurable_inl).comp measurable_fst
    · exact measurable_inr.comp measurable_inr

def cavityGeneratedOriginPayloadFreeClock (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedOriginSelection U.tree → Paper.Overlap
  | .inl _ => 0
  | .inr (.inl z) => z.2
  | .inr (.inr _) => 0

theorem measurable_cavityGeneratedOriginPayloadFreeClock
    (U : CavityGeneratedConstructedComponent m) :
    Measurable (cavityGeneratedOriginPayloadFreeClock U) := by
  exact measurable_const.sumElim (measurable_snd.sumElim measurable_const)

private theorem generatedOriginChartSingleton
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) :
    MeasurableSet ({γ} : Set (PrintedGeneratedOriginChart U)) := by
  rcases γ with i | (i | u)
  · have hh : MeasurableSet
        (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginForkVertices U.tree).length)) :
          Set (PrintedGeneratedOriginChart U)) := (measurableSet_singleton i).inl_image
    simpa only [Set.image_singleton] using hh
  · have hi : MeasurableSet
        (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginEdges U.tree).length)) :
          Set (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)) :=
      (measurableSet_singleton i).inl_image
    have hh : MeasurableSet
        (Sum.inr '' (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginEdges U.tree).length))) :
          Set (PrintedGeneratedOriginChart U)) := hi.inr_image
    simpa only [Set.image_singleton] using hh
  · have hi : MeasurableSet
        (Sum.inr '' ({u} : Set Unit) :
          Set (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)) :=
      (measurableSet_singleton u).inr_image
    have hh : MeasurableSet
        (Sum.inr '' (Sum.inr '' ({u} : Set Unit)) : Set (PrintedGeneratedOriginChart U)) :=
      hi.inr_image
    simpa only [Set.image_singleton] using hh

def cavityGeneratedSingleOriginChartEvent
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) :
    Set (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :=
  {z | cavityGeneratedOriginPayloadChart (W.component c) z.2 = γ ∧
    z.1 ∈ W.clockTemplate.orderSet ∧
    printedGeneratedOriginChartCell (W.component c) γ z.1
      (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2)}

theorem measurableSet_cavityGeneratedSingleOriginChartEvent
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) :
    MeasurableSet (cavityGeneratedSingleOriginChartEvent W c γ) := by
  have hclass : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      cavityGeneratedOriginPayloadChart (W.component c) z.2 = γ} :=
    (generatedOriginChartSingleton _ γ).preimage
      ((measurable_cavityGeneratedOriginPayloadChart _).comp measurable_snd)
  have hold := W.clockTemplate.isClosed_orderSet.measurableSet.preimage
    (measurable_fst : Measurable
      (Prod.fst : CavityGeneratedHistory Paper.Overlap m ×
        CavityGeneratedOriginSelection (W.tree c) → CavityGeneratedHistory Paper.Overlap m))
  have hcell : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      printedGeneratedOriginChartCell (W.component c) γ z.1
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2)} := by
    rcases γ with i | (i | u)
    · exact MeasurableSet.univ
    · have hr : Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) =>
            cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) :=
        (measurable_cavityGeneratedOriginPayloadFreeClock (W.component c)).comp measurable_snd
      have hq (j : ℕ) :=
        (nativeStreamingGeneratedComponentClock_continuous (W.component c) j).measurable.comp
          (measurable_fst : Measurable
            (Prod.fst : CavityGeneratedHistory Paper.Overlap m ×
              CavityGeneratedOriginSelection (W.tree c) → CavityGeneratedHistory Paper.Overlap m))
      exact (measurableSet_le (measurable_subtype_coe.comp (hq _))
        (measurable_subtype_coe.comp hr)).inter
          (measurableSet_le (measurable_subtype_coe.comp hr)
            (measurable_subtype_coe.comp (hq _)))
    · exact MeasurableSet.univ
  exact hclass.inter (hold.inter hcell)

def cavityGeneratedSingleOriginChartForest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedConstructedForest (m+1) :=
  cavityGeneratedForestOfComponents (Function.update (W.reindex Fin.castSucc).component c
    (printedGeneratedOriginChartComponent (W.component c) γ k))

theorem cavityGeneratedSingleOriginChartForest_leafCount
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind) :
    cavityGeneratedForestLeafCount (cavityGeneratedSingleOriginChartForest W c γ k) =
      cavityGeneratedForestLeafCount W + k.newLeafCount := by
  have he := cavityGeneratedForestLeafCount_replace_component (W.reindex Fin.castSucc) c
    (printedGeneratedOriginChartComponent (W.component c) γ k)
  have hc := printedGeneratedOriginChartComponent_leafCount (W.component c) γ k
  change cavityGeneratedForestLeafCount (cavityGeneratedSingleOriginChartForest W c γ k) +
    cavityGeneratedComponentLeafCount (W.component c) =
    cavityGeneratedForestLeafCount W +
      cavityGeneratedComponentLeafCount (printedGeneratedOriginChartComponent (W.component c) γ k) at he
  omega

theorem cavityGeneratedSingleOriginChartForest_leafCount_le
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind) :
    cavityGeneratedForestLeafCount (cavityGeneratedSingleOriginChartForest W c γ k) ≤
      cavityGeneratedForestLeafCount W + 2 := by
  rw [cavityGeneratedSingleOriginChartForest_leafCount]
  cases k <;> simp only [NativeStreamingGeneratedVertexKind.newLeafCount] <;> omega

def cavityGeneratedSingleOriginChartMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+1)) :=
  ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).restrict
    (cavityGeneratedSingleOriginChartEvent W c γ)).map
      (fun z => Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z))

theorem cavityGeneratedSingleOriginChartEvent_disjoint
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Pairwise (Disjoint on (cavityGeneratedSingleOriginChartEvent W c)) := by
  intro γ δ hne
  apply Set.disjoint_left.mpr
  intro z hz hδ
  exact hne (hz.1.symm.trans hδ.1)


theorem cavityGeneratedForest_component_rawClock
    (W : CavityGeneratedConstructedForest m) (h : CavityGeneratedHistory Paper.Overlap m)
    (c : Fin W.componentCount) (j : ℕ) :
    (cavityGeneratedFiniteClockLabels (W.component c).label j).value h =
      W.clockTemplate.rawClock h c j := by
  by_cases hj : j ≤ W.depth c
  · simp only [cavityGeneratedFiniteClockLabels,CavityGeneratedConstructedForest.component,
      CavityGeneratedConstructedForest.clockTemplate,CavityGeneratedForestClockTemplate.rawClock,
      dif_pos hj]
  · simp only [cavityGeneratedFiniteClockLabels,CavityGeneratedConstructedForest.component,
      CavityGeneratedConstructedForest.clockTemplate,CavityGeneratedForestClockTemplate.rawClock,
      dif_neg hj,CavityGeneratedClockLabel.value]

theorem cavityGeneratedForest_orderSet_iff_components
    (W : CavityGeneratedConstructedForest m) (h : CavityGeneratedHistory Paper.Overlap m) :
    h ∈ W.clockTemplate.orderSet ↔
      ∀c, h ∈ nativeStreamingGeneratedComponentOrderSet (W.component c) := by
  change (∀c,∀j : Fin (W.depth c), _ ≤ _) ↔
    (∀c,∀j : Fin (W.depth c), _ ≤ _)
  simp only [cavityGeneratedForest_component_rawClock]

theorem cavityGeneratedOriginSelectionClock_eq_chart
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedOriginSelectionClock W c z =
      printedGeneratedOriginChartClock (W.component c)
        (cavityGeneratedOriginPayloadChart (W.component c) z.2) z.1
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
  have he : W.clockTemplate.clock z.1 c =
      nativeStreamingGeneratedComponentClock (W.component c) z.1 :=
    (printedGeneratedComponentClock_eq_native (W.component c) z.1)
  rcases z with ⟨h,g⟩
  rcases g with i | (i | u) <;>
    simp only [cavityGeneratedOriginSelectionClock,cavityGeneratedOriginSelectionOrigin,
      nativeStreamingOriginLevel,cavityGeneratedOriginPayloadChart,
      cavityGeneratedOriginPayloadFreeClock,printedGeneratedOriginChartClock,
      printedGeneratedOriginChartFork,printedGeneratedOriginChartEdge,he] <;> rfl

theorem cavityGeneratedSingleOriginChart_append_measurable
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) =>
        (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z) :
          CavityGeneratedHistory Paper.Overlap (m+1))) := by
  exact cavityGeneratedHistoryAppend_measurable.comp
    (measurable_fst.prodMk (measurable_cavityGeneratedOriginSelectionClock W c))

theorem cavityGeneratedSingleOriginChartMeasure_sum_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    (∑γ, cavityGeneratedSingleOriginChartMeasure μ a W c M γ) ≤
      (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).map
        (fun z => Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z)) := by
  classical
  unfold cavityGeneratedSingleOriginChartMeasure
  rw [←Measure.map_finset_sum' (cavityGeneratedSingleOriginChart_append_measurable W c).aemeasurable,
    ←Measure.sum_fintype,←Measure.restrict_iUnion
      (cavityGeneratedSingleOriginChartEvent_disjoint W c)
      (measurableSet_cavityGeneratedSingleOriginChartEvent W c)]
  exact Measure.map_mono Measure.restrict_le_self
    (cavityGeneratedSingleOriginChart_append_measurable W c)

theorem cavityGeneratedSingleOriginChartForest_append_order
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z ∈ cavityGeneratedSingleOriginChartEvent W c γ) :
    Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z) ∈
      (cavityGeneratedSingleOriginChartForest W c γ k).clockTemplate.orderSet := by
  classical
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z)
  have ho : H ∈ (W.reindex Fin.castSucc).clockTemplate.orderSet := by
    rw [W.reindex_orderSet]
    simpa only [Set.mem_preimage,Function.comp_def,H,Fin.snoc_castSucc] using hz.2.1
  apply (cavityGeneratedForest_orderSet_iff_components _ H).mpr
  change ∀d : Fin W.componentCount, H ∈ nativeStreamingGeneratedComponentOrderSet
    (Function.update (W.reindex Fin.castSucc).component c
      (printedGeneratedOriginChartComponent (W.component c) γ k) d)
  intro d
  by_cases hd : d = c
  · subst d
    rw [Function.update_self]
    have hc := printedGeneratedOriginChartComponent_snoc_order (W.component c) γ k z.1
      (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2)
      ((cavityGeneratedForest_orderSet_iff_components W z.1).mp hz.2.1 c) hz.2.2
    have ht : cavityGeneratedOriginSelectionClock W c z =
        printedGeneratedOriginChartClock (W.component c) γ z.1
          (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
      rw [cavityGeneratedOriginSelectionClock_eq_chart,hz.1]
    simpa only [H,ht] using hc
  · rw [Function.update_of_ne hd]
    exact (cavityGeneratedForest_orderSet_iff_components _ H).mp ho d

theorem cavityGeneratedSingleOriginChartMeasure_order
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind) :
    ∀ᵐh ∂cavityGeneratedSingleOriginChartMeasure μ a W c M γ,
      h ∈ (cavityGeneratedSingleOriginChartForest W c γ k).clockTemplate.orderSet := by
  unfold cavityGeneratedSingleOriginChartMeasure
  apply (ae_map_iff (cavityGeneratedSingleOriginChart_append_measurable W c).aemeasurable
    (show MeasurableSet {h : CavityGeneratedHistory Paper.Overlap (m+1) |
      h ∈ (cavityGeneratedSingleOriginChartForest W c γ k).clockTemplate.orderSet} from
        (cavityGeneratedSingleOriginChartForest W c γ k).clockTemplate.isClosed_orderSet.measurableSet)).mpr
  exact (ae_restrict_mem (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ)).mono
    (fun z hz => cavityGeneratedSingleOriginChartForest_append_order W c γ k z hz)

theorem cavityGeneratedSingleOriginChartMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (∑γ, cavityGeneratedSingleOriginChartMeasure μ a W c M γ)
      cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*C) :=
  cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _
    (cavityGeneratedOriginSelectionKernel_appended_history_budget μ a ha hμ W c M C hM horder)
    (cavityGeneratedSingleOriginChartMeasure_sum_le μ a W c M)

end QuantitativeFollowup
