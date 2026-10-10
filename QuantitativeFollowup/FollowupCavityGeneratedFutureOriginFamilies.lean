module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionKernel
public import QuantitativeFollowup.SupportingGeneratedOriginFutureComponentCharts
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponentReplacementRetained

@[expose] public section

/-! A future attachment retains the actual selected-origin payload and
then draws an independent free mark. Both cells are evaluated at the
original history. Restriction preserves the actual normalized budget,
including inherited forks and the root contribution. -/
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

local instance futureOriginChartMeasurableSpace (U : CavityGeneratedConstructedComponent m) :
    MeasurableSpace (PrintedGeneratedOriginChart U) :=
  inferInstanceAs (MeasurableSpace (Fin (cavityGeneratedOriginForkVertices U.tree).length ⊕
    (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)))

def futureOriginPayloadChart (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedOriginSelection U.tree → PrintedGeneratedOriginChart U
  | .inl i => .inl i
  | .inr (.inl z) => .inr (.inl z.1)
  | .inr (.inr u) => .inr (.inr u)

private theorem futureOriginPayloadChart_measurable
    (U : CavityGeneratedConstructedComponent m) :
    Measurable (futureOriginPayloadChart U) := by
  apply measurable_fun_sum
  · exact measurable_inl
  · apply measurable_fun_sum
    · exact (measurable_inr.comp measurable_inl).comp measurable_fst
    · exact measurable_inr.comp measurable_inr

def futureOriginPayloadFreeClock (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedOriginSelection U.tree → Paper.Overlap
  | .inl _ => 0
  | .inr (.inl z) => z.2
  | .inr (.inr _) => 0

private theorem futureOriginPayloadFreeClock_measurable
    (U : CavityGeneratedConstructedComponent m) :
    Measurable (futureOriginPayloadFreeClock U) :=
  measurable_const.sumElim (measurable_snd.sumElim measurable_const)

private theorem futureOriginChartSingleton
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
        (Sum.inr '' ({u} : Set Unit) : Set (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)) :=
      (measurableSet_singleton u).inr_image
    have hh : MeasurableSet
        (Sum.inr '' (Sum.inr '' ({u} : Set Unit)) : Set (PrintedGeneratedOriginChart U)) :=
      hi.inr_image
    simpa only [Set.image_singleton] using hh

private theorem futureOrigin_component_rawClock
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

private theorem futureOrigin_orderSet_iff_components
    (W : CavityGeneratedConstructedForest m) (h : CavityGeneratedHistory Paper.Overlap m) :
    h ∈ W.clockTemplate.orderSet ↔
      ∀c, h ∈ nativeStreamingGeneratedComponentOrderSet (W.component c) := by
  change (∀c,∀j : Fin (W.depth c), _ ≤ _) ↔ (∀c,∀j : Fin (W.depth c), _ ≤ _)
  simp only [futureOrigin_component_rawClock]

private theorem futureOriginSelectionClock_eq_chart
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedOriginSelectionClock W c z =
      printedGeneratedOriginChartClock (W.component c)
        (futureOriginPayloadChart (W.component c) z.2) z.1
        (futureOriginPayloadFreeClock (W.component c) z.2) := by
  have he : W.clockTemplate.clock z.1 c =
      nativeStreamingGeneratedComponentClock (W.component c) z.1 :=
    printedGeneratedComponentClock_eq_native (W.component c) z.1
  rcases z with ⟨h,g⟩
  rcases g with i | (i | u) <;>
    simp only [cavityGeneratedOriginSelectionClock,cavityGeneratedOriginSelectionOrigin,
      nativeStreamingOriginLevel,futureOriginPayloadChart,futureOriginPayloadFreeClock,
      printedGeneratedOriginChartClock,printedGeneratedOriginChartFork,
      printedGeneratedOriginChartEdge,he] <;> rfl

def cavityGeneratedFutureOriginChartEvent
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    Set ((CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap) :=
  {z | futureOriginPayloadChart (W.component c) z.1.2 = γ ∧
    z.1.1 ∈ W.clockTemplate.orderSet ∧
    printedGeneratedOriginChartCell (W.component c) γ z.1.1
      (futureOriginPayloadFreeClock (W.component c) z.1.2) ∧
    (nativeStreamingGeneratedComponentClock (W.component c) z.1.1 (j.val+1) ≤ z.2 ∧
      z.2 ≤ nativeStreamingGeneratedComponentClock (W.component c) z.1.1 j) ∧
    cavityGeneratedOriginSelectionClock W c z.1 < z.2}

theorem measurableSet_cavityGeneratedFutureOriginChartEvent
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    MeasurableSet (cavityGeneratedFutureOriginChartEvent W c γ j) := by
  let Z := (CavityGeneratedHistory Paper.Overlap m ×
    CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap
  have hh : Measurable (fun z : Z => z.1.1) := measurable_fst.comp measurable_fst
  have hg : Measurable (fun z : Z => z.1.2) := measurable_snd.comp measurable_fst
  have hq (p : ℕ) : Measurable (fun z : Z =>
      nativeStreamingGeneratedComponentClock (W.component c) z.1.1 p) :=
    (nativeStreamingGeneratedComponentClock_continuous (W.component c) p).measurable.comp hh
  have hr : Measurable (fun z : Z => futureOriginPayloadFreeClock (W.component c) z.1.2) :=
    (futureOriginPayloadFreeClock_measurable (W.component c)).comp hg
  have hqr (p : ℕ) := measurable_subtype_coe.comp (hq p)
  have hrr := measurable_subtype_coe.comp hr
  have hclass : MeasurableSet {z : Z | futureOriginPayloadChart (W.component c) z.1.2 = γ} :=
    (futureOriginChartSingleton _ γ).preimage
      ((futureOriginPayloadChart_measurable _).comp hg)
  have hold := W.clockTemplate.isClosed_orderSet.measurableSet.preimage hh
  have hcell : MeasurableSet {z : Z | printedGeneratedOriginChartCell (W.component c) γ
      z.1.1 (futureOriginPayloadFreeClock (W.component c) z.1.2)} := by
    rcases γ with i | (i | u)
    · exact MeasurableSet.univ
    · exact (measurableSet_le (hqr _) hrr).inter (measurableSet_le hrr (hqr _))
    · exact MeasurableSet.univ
  have hfuture := measurableSet_lt
    ((measurable_cavityGeneratedOriginSelectionClock W c).comp measurable_fst)
    (measurable_snd : Measurable (Prod.snd : Z → Paper.Overlap))
  exact hclass.inter (hold.inter (hcell.inter
    (((measurableSet_le (hq _) measurable_snd).inter
      (measurableSet_le measurable_snd (hq _))).inter hfuture)))

def cavityGeneratedFutureOriginChartForest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    CavityGeneratedConstructedForest (m+2) :=
  cavityGeneratedForestOfComponents (Function.update
    (W.reindex (fun i => i.castSucc.castSucc)).component c
    (printedGeneratedOriginFutureChartComponent (W.component c) γ j))

theorem cavityGeneratedFutureOriginChartForest_leafCount
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    cavityGeneratedForestLeafCount (cavityGeneratedFutureOriginChartForest W c γ j) =
      cavityGeneratedForestLeafCount W + 2 := by
  have he := cavityGeneratedForestLeafCount_replace_component
    (W.reindex (fun i => i.castSucc.castSucc)) c
    (printedGeneratedOriginFutureChartComponent (W.component c) γ j)
  have hc := printedGeneratedOriginFutureChartComponent_leafCount (W.component c) γ j
  change cavityGeneratedForestLeafCount (cavityGeneratedFutureOriginChartForest W c γ j) +
    cavityGeneratedComponentLeafCount (W.component c) =
    cavityGeneratedForestLeafCount W +
      cavityGeneratedComponentLeafCount (printedGeneratedOriginFutureChartComponent (W.component c) γ j) at he
  omega

def cavityGeneratedFutureOriginChartAppend
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap) :
    CavityGeneratedHistory Paper.Overlap (m+2) :=
  nativeStreamingGeneratedCrossEdgeAppend z.1.1
    (cavityGeneratedOriginSelectionClock W c z.1) z.2

theorem measurable_cavityGeneratedFutureOriginChartAppend
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Measurable (cavityGeneratedFutureOriginChartAppend W c) := by
  have hfirst : Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) =>
      (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z) :
        CavityGeneratedHistory Paper.Overlap (m+1))) :=
    cavityGeneratedHistoryAppend_measurable.comp
      (measurable_fst.prodMk (measurable_cavityGeneratedOriginSelectionClock W c))
  exact cavityGeneratedHistoryAppend_measurable.comp (hfirst.prodMap measurable_id)

def cavityGeneratedFutureOriginChartMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+2)) :=
  (((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
    Kernel.const _ (parisiFreeMeasure μ a)).restrict
      (cavityGeneratedFutureOriginChartEvent W c γ j)).map
        (cavityGeneratedFutureOriginChartAppend W c)

theorem cavityGeneratedFutureOriginChartForest_append_order
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartEvent W c γ j) :
    cavityGeneratedFutureOriginChartAppend W c z ∈
      (cavityGeneratedFutureOriginChartForest W c γ j).clockTemplate.orderSet := by
  classical
  let H := cavityGeneratedFutureOriginChartAppend W c z
  have ho : H ∈ (W.reindex (fun i => i.castSucc.castSucc)).clockTemplate.orderSet := by
    rw [W.reindex_orderSet]
    simpa only [Set.mem_preimage,Function.comp_def,H,cavityGeneratedFutureOriginChartAppend,
      nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_castSucc] using hz.2.1
  apply (futureOrigin_orderSet_iff_components _ H).mpr
  change ∀d : Fin W.componentCount, H ∈ nativeStreamingGeneratedComponentOrderSet
    (Function.update (W.reindex (fun i => i.castSucc.castSucc)).component c
      (printedGeneratedOriginFutureChartComponent (W.component c) γ j) d)
  intro d
  by_cases hd : d = c
  · subst d
    rw [Function.update_self]
    have ht : cavityGeneratedOriginSelectionClock W c z.1 =
        printedGeneratedOriginChartClock (W.component c) γ z.1.1
          (futureOriginPayloadFreeClock (W.component c) z.1.2) := by
      rw [futureOriginSelectionClock_eq_chart,hz.1]
    have hc := printedGeneratedOriginFutureChartComponent_append_order (W.component c) γ j
      z.1.1 (futureOriginPayloadFreeClock (W.component c) z.1.2) z.2
      ((futureOrigin_orderSet_iff_components W z.1.1).mp hz.2.1 c)
      hz.2.2.1 hz.2.2.2.1 (by simpa only [ht] using hz.2.2.2.2)
    simpa only [H,cavityGeneratedFutureOriginChartAppend,ht] using hc
  · rw [Function.update_of_ne hd]
    exact (futureOrigin_orderSet_iff_components _ H).mp ho d

theorem cavityGeneratedFutureOriginChartMeasure_order
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    ∀ᵐh ∂cavityGeneratedFutureOriginChartMeasure μ a W c M γ j,
      h ∈ (cavityGeneratedFutureOriginChartForest W c γ j).clockTemplate.orderSet := by
  unfold cavityGeneratedFutureOriginChartMeasure
  apply (ae_map_iff (measurable_cavityGeneratedFutureOriginChartAppend W c).aemeasurable
    (show MeasurableSet {h : CavityGeneratedHistory Paper.Overlap (m+2) |
      h ∈ (cavityGeneratedFutureOriginChartForest W c γ j).clockTemplate.orderSet} from
        (cavityGeneratedFutureOriginChartForest W c γ j).clockTemplate.isClosed_orderSet.measurableSet)).mpr
  exact (ae_restrict_mem (measurableSet_cavityGeneratedFutureOriginChartEvent W c γ j)).mono
    (fun z hz => cavityGeneratedFutureOriginChartForest_append_order W c γ j z hz)

theorem cavityGeneratedFutureOriginChartMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedFutureOriginChartMeasure μ a W c M γ j) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*C) := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  have hB := cavityGeneratedOriginSelectionKernel_payload_budget μ a ha hμ W c M C hM horder
  have hF := cavityGeneratedMarkBudget_fresh (parisiFreeMeasure μ a)
    (cavityGenerated_free_mass_le_one μ a ha.1) (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c)
    (cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks
      (cavityGeneratedOriginSelectionClock W c))
    (cavityGeneratedPayloadExtendedMarks_measurable cavityGeneratedHistoryMarks
      cavityGeneratedHistoryMarks_measurable _ (measurable_cavityGeneratedOriginSelectionClock W c))
    _ hB (cavityGeneratedFutureOriginChartEvent W c γ j)
  unfold cavityGeneratedFutureOriginChartMeasure
  rw [Measure.compProd_const]
  apply cavityGeneratedMarkBudget_map (parisiFreeMeasure μ a) _ _ _
    cavityGeneratedHistoryMarks_measurable _ hF (cavityGeneratedFutureOriginChartAppend W c)
    (measurable_cavityGeneratedFutureOriginChartAppend W c)
  intro i
  funext z
  cases i using Fin.lastCases with
  | last =>
      simp only [Function.comp_apply,cavityGeneratedHistoryMarks,
        cavityGeneratedFutureOriginChartAppend,nativeStreamingGeneratedCrossEdgeAppend,
        cavityGeneratedExtendedMarks,Fin.snoc_last]
  | cast i =>
      cases i using Fin.lastCases <;>
        simp only [Function.comp_apply,cavityGeneratedHistoryMarks,
          cavityGeneratedFutureOriginChartAppend,nativeStreamingGeneratedCrossEdgeAppend,
          cavityGeneratedExtendedMarks,cavityGeneratedPayloadExtendedMarks,
          Fin.snoc_last,Fin.snoc_castSucc]

/- The source partition uses half-open original future cells. Its lower
endpoint is assigned to the next cell, while repeated cells stay empty. -/
def cavityGeneratedFutureOriginChartSourceEvent
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    Set ((CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap) :=
  cavityGeneratedFutureOriginChartEvent W c γ j ∩
    {z | nativeStreamingGeneratedComponentClock (W.component c) z.1.1 (j.val+1) < z.2}

theorem measurableSet_cavityGeneratedFutureOriginChartSourceEvent
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    MeasurableSet (cavityGeneratedFutureOriginChartSourceEvent W c γ j) := by
  have hq : Measurable (fun z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap =>
      nativeStreamingGeneratedComponentClock (W.component c) z.1.1 (j.val+1)) :=
    (nativeStreamingGeneratedComponentClock_continuous (W.component c) (j.val+1)).measurable.comp
      (measurable_fst.comp measurable_fst)
  exact (measurableSet_cavityGeneratedFutureOriginChartEvent W c γ j).inter
    (measurableSet_lt hq measurable_snd)

theorem cavityGeneratedFutureOriginChartSourceEvent_future_cell
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j) :
    z.2 ∈ Ioc (nativeStreamingGeneratedComponentClock (W.component c) z.1.1 (j.val+1))
      (nativeStreamingGeneratedComponentClock (W.component c) z.1.1 j) :=
  ⟨hz.2,hz.1.2.2.2.1.2⟩

def cavityGeneratedFutureOriginChartSourceMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+2)) :=
  (((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
    Kernel.const _ (parisiFreeMeasure μ a)).restrict
      (cavityGeneratedFutureOriginChartSourceEvent W c γ j)).map
        (cavityGeneratedFutureOriginChartAppend W c)

theorem cavityGeneratedFutureOriginChartSourceMeasure_eq_product
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j =
      (((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).prod (parisiFreeMeasure μ a)).restrict
        (cavityGeneratedFutureOriginChartSourceEvent W c γ j)).map
          (cavityGeneratedFutureOriginChartAppend W c) := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  unfold cavityGeneratedFutureOriginChartSourceMeasure
  rw [Measure.compProd_const]

theorem cavityGeneratedFutureOriginChartSourceMeasure_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j ≤
      cavityGeneratedFutureOriginChartMeasure μ a W c M γ j :=
  Measure.map_mono (Measure.restrict_mono (inter_subset_left) le_rfl)
    (measurable_cavityGeneratedFutureOriginChartAppend W c)

theorem cavityGeneratedFutureOriginChartSourceMeasure_order
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c)) :
    ∀ᵐh ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j,
      h ∈ (cavityGeneratedFutureOriginChartForest W c γ j).clockTemplate.orderSet :=
  (cavityGeneratedFutureOriginChartMeasure_order μ a W c M γ j).filter_mono
    (ae_mono (cavityGeneratedFutureOriginChartSourceMeasure_le μ a W c M γ j))

theorem cavityGeneratedFutureOriginChartSourceMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*C) :=
  cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _
    (cavityGeneratedFutureOriginChartMeasure_budget μ a ha hμ W c M γ j C hM horder)
    (cavityGeneratedFutureOriginChartSourceMeasure_le μ a W c M γ j)

end QuantitativeFollowup
