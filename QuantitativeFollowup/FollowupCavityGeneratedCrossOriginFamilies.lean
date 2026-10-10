module
public import QuantitativeFollowup.SupportingGeneratedOriginCrossComponentCharts
public import QuantitativeFollowup.FollowupCavityGeneratedOriginDoubleSelection
public import QuantitativeFollowup.FollowupCavityGeneratedMarkProgramBudget

@[expose] public section

/-! Both selected payloads belong to the same original component and original
history.  Chart restriction precedes the double append.  A non-edge pair uses
one canonical chart, while two edges use the genuine four-way partition. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

local instance crossOriginChartMeasurableSpace (U : CavityGeneratedConstructedComponent m) :
    MeasurableSpace (PrintedGeneratedOriginChart U) :=
  inferInstanceAs (MeasurableSpace (Fin (cavityGeneratedOriginForkVertices U.tree).length ⊕
    (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)))

private theorem crossOriginMeasurableSet_const {Z : Type*} [MeasurableSpace Z] (p : Prop) :
    MeasurableSet {z : Z | p} := by
  by_cases hp : p <;> simp only [hp, Set.setOf_true, Set.setOf_false]
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

abbrev CavityGeneratedCrossOriginPayload (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) :=
  (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
    CavityGeneratedOriginSelection (W.tree c)

def crossOriginPayloadChart (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedOriginSelection U.tree → PrintedGeneratedOriginChart U
  | .inl i => .inl i
  | .inr (.inl z) => .inr (.inl z.1)
  | .inr (.inr u) => .inr (.inr u)

private theorem crossOriginPayloadChart_measurable (U : CavityGeneratedConstructedComponent m) :
    Measurable (crossOriginPayloadChart U) := by
  apply measurable_fun_sum
  · exact measurable_inl
  · apply measurable_fun_sum
    · exact (measurable_inr.comp measurable_inl).comp measurable_fst
    · exact measurable_inr.comp measurable_inr

def crossOriginFreeClock (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedOriginSelection U.tree → Paper.Overlap
  | .inl _ => 0
  | .inr (.inl z) => z.2
  | .inr (.inr _) => 0

private theorem crossOriginFreeClock_measurable (U : CavityGeneratedConstructedComponent m) :
    Measurable (crossOriginFreeClock U) :=
  measurable_const.sumElim (measurable_snd.sumElim measurable_const)

private theorem crossOriginChartSingleton (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) : MeasurableSet ({γ} : Set (PrintedGeneratedOriginChart U)) := by
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
  · have hi : MeasurableSet (Sum.inr '' ({u} : Set Unit) :
        Set (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)) :=
      (measurableSet_singleton u).inr_image
    have hh : MeasurableSet (Sum.inr '' (Sum.inr '' ({u} : Set Unit)) :
        Set (PrintedGeneratedOriginChart U)) := hi.inr_image
    simpa only [Set.image_singleton] using hh

def crossOriginSingleEvent (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c)) :
    Set (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :=
  {z | crossOriginPayloadChart (W.component c) z.2 = γ ∧
    z.1 ∈ W.clockTemplate.orderSet ∧
    printedGeneratedOriginChartCell (W.component c) γ z.1
      (crossOriginFreeClock (W.component c) z.2)}

private theorem crossOriginSingleEvent_measurable (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c)) :
    MeasurableSet (crossOriginSingleEvent W c γ) := by
  have hclass : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      crossOriginPayloadChart (W.component c) z.2 = γ} :=
    (crossOriginChartSingleton _ γ).preimage
      ((crossOriginPayloadChart_measurable _).comp measurable_snd)
  have hold := W.clockTemplate.isClosed_orderSet.measurableSet.preimage
    (measurable_fst : Measurable (Prod.fst : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) → CavityGeneratedHistory Paper.Overlap m))
  have hcell : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      printedGeneratedOriginChartCell (W.component c) γ z.1
        (crossOriginFreeClock (W.component c) z.2)} := by
    rcases γ with i | (i | u)
    · exact MeasurableSet.univ
    · have hr : Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) => crossOriginFreeClock (W.component c) z.2) :=
        (crossOriginFreeClock_measurable (W.component c)).comp measurable_snd
      have hq (j : ℕ) : Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) =>
          nativeStreamingGeneratedComponentClock (W.component c) z.1 j) :=
        (nativeStreamingGeneratedComponentClock_continuous (W.component c) j).measurable.comp
          (measurable_fst : Measurable (Prod.fst : CavityGeneratedHistory Paper.Overlap m ×
            CavityGeneratedOriginSelection (W.tree c) → CavityGeneratedHistory Paper.Overlap m))
      exact (measurableSet_le (measurable_subtype_coe.comp (hq _)) (measurable_subtype_coe.comp hr)).inter
        (measurableSet_le (measurable_subtype_coe.comp hr) (measurable_subtype_coe.comp (hq _)))
    · exact MeasurableSet.univ
  exact hclass.inter (hold.inter hcell)

def crossOriginChartActive (U : CavityGeneratedConstructedComponent m)
    (γ₁ γ₂ : PrintedGeneratedOriginChart U) (k : NativeStreamingGeneratedCrossEdgeChart)
    (r l : Paper.Overlap) : Prop := match γ₁, γ₂ with
  | .inr (.inl i), .inr (.inl j) =>
      k.Holds (printedGeneratedOriginChartEdge U i).depth (printedGeneratedOriginChartEdge U j).depth r l
  | _, _ => k = .apart

private theorem crossOriginChartActive_structural (U : CavityGeneratedConstructedComponent m)
    (γ₁ γ₂ : PrintedGeneratedOriginChart U) (k : NativeStreamingGeneratedCrossEdgeChart)
    (r l : Paper.Overlap) (hk : crossOriginChartActive U γ₁ γ₂ k r l) :
    printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l := by
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  all_goals first | exact hk | trivial

def cavityGeneratedCrossOriginChartEvent (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c))
    (k : NativeStreamingGeneratedCrossEdgeChart) : Set (CavityGeneratedCrossOriginPayload W c) :=
  {z | z.1 ∈ crossOriginSingleEvent W c γ₁ ∧
    (z.1.1, z.2) ∈ crossOriginSingleEvent W c γ₂ ∧
    crossOriginChartActive (W.component c) γ₁ γ₂ k
      (crossOriginFreeClock (W.component c) z.1.2) (crossOriginFreeClock (W.component c) z.2)}

theorem measurableSet_cavityGeneratedCrossOriginChartEvent (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c))
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    MeasurableSet (cavityGeneratedCrossOriginChartEvent W c γ₁ γ₂ k) := by
  have hfirst := (crossOriginSingleEvent_measurable W c γ₁).preimage
    (measurable_fst : Measurable (Prod.fst : CavityGeneratedCrossOriginPayload W c → _))
  have hsecond := (crossOriginSingleEvent_measurable W c γ₂).preimage
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd :
      Measurable (fun z : CavityGeneratedCrossOriginPayload W c => (z.1.1, z.2)))
  have hactive : MeasurableSet {z : CavityGeneratedCrossOriginPayload W c |
      crossOriginChartActive (W.component c) γ₁ γ₂ k
        (crossOriginFreeClock (W.component c) z.1.2) (crossOriginFreeClock (W.component c) z.2)} := by
    have hr := (crossOriginFreeClock_measurable (W.component c)).comp
      (measurable_snd.comp measurable_fst : Measurable
        (fun z : CavityGeneratedCrossOriginPayload W c => z.1.2))
    have hl := (crossOriginFreeClock_measurable (W.component c)).comp
      (measurable_snd : Measurable (Prod.snd : CavityGeneratedCrossOriginPayload W c → _))
    rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
    all_goals try exact crossOriginMeasurableSet_const (k = .apart)
    cases k with
    | lt => exact (crossOriginMeasurableSet_const _).inter (measurableSet_lt (measurable_subtype_coe.comp hr) (measurable_subtype_coe.comp hl))
    | equal => exact (crossOriginMeasurableSet_const _).inter (measurableSet_eq_fun hr hl)
    | gt => exact (crossOriginMeasurableSet_const _).inter (measurableSet_lt (measurable_subtype_coe.comp hl) (measurable_subtype_coe.comp hr))
    | apart => exact crossOriginMeasurableSet_const _
  exact hfirst.inter (hsecond.inter hactive)

def cavityGeneratedCrossOriginAppend (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (z : CavityGeneratedCrossOriginPayload W c) :
    CavityGeneratedHistory Paper.Overlap (m+2) :=
  Fin.snoc (Fin.snoc z.1.1 (cavityGeneratedOriginSelectionClock W c z.1))
    (cavityGeneratedOriginSecondSelectionClock W c z)

theorem measurable_cavityGeneratedCrossOriginAppend (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) : Measurable (cavityGeneratedCrossOriginAppend W c) := by
  have hfirst : Measurable (fun z : CavityGeneratedCrossOriginPayload W c =>
      (Fin.snoc z.1.1 (cavityGeneratedOriginSelectionClock W c z.1) :
        CavityGeneratedHistory Paper.Overlap (m+1))) :=
    cavityGeneratedHistoryAppend_measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_cavityGeneratedOriginSelectionClock W c).comp measurable_fst))
  exact cavityGeneratedHistoryAppend_measurable.comp
    (hfirst.prodMk (measurable_cavityGeneratedOriginSecondSelectionClock W c))

def cavityGeneratedCrossOriginChartForest (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c))
    (k : NativeStreamingGeneratedCrossEdgeChart) : CavityGeneratedConstructedForest (m+2) :=
  cavityGeneratedForestOfComponents
    (Function.update (W.reindex (fun i => i.castSucc.castSucc)).component c
      (printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k))

theorem cavityGeneratedCrossOriginChartForest_same (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c))
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).component c =
      printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k := by
  classical
  unfold cavityGeneratedCrossOriginChartForest
  rw [cavityGeneratedForestOfComponents_component]
  exact Function.update_self _ _ _

theorem cavityGeneratedCrossOriginChartForest_other (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c))
    (k : NativeStreamingGeneratedCrossEdgeChart) (d : Fin W.componentCount) (hd : d ≠ c) :
    (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).component d =
      (W.reindex (fun i => i.castSucc.castSucc)).component d := by
  classical
  unfold cavityGeneratedCrossOriginChartForest
  rw [cavityGeneratedForestOfComponents_component]
  exact Function.update_of_ne hd _ _

theorem cavityGeneratedCrossOriginChartForest_leafCount (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c))
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    cavityGeneratedForestLeafCount (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k) =
      cavityGeneratedForestLeafCount W + 2 := by
  have he := cavityGeneratedForestLeafCount_replace_component
    (W.reindex (fun i => i.castSucc.castSucc)) c
    (printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k)
  have hc := printedGeneratedOriginCrossChartComponent_leafCount (W.component c) γ₁ γ₂ k
  change cavityGeneratedForestLeafCount (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k) +
    cavityGeneratedComponentLeafCount (W.component c) =
      cavityGeneratedForestLeafCount W +
        cavityGeneratedComponentLeafCount (printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k) at he
  omega

private theorem crossOriginComponentRawClock (W : CavityGeneratedConstructedForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) (j : ℕ) :
    (cavityGeneratedFiniteClockLabels (W.component c).label j).value h =
      W.clockTemplate.rawClock h c j := by
  by_cases hj : j ≤ W.depth c
  · simp only [cavityGeneratedFiniteClockLabels, CavityGeneratedConstructedForest.component,
      CavityGeneratedConstructedForest.clockTemplate, CavityGeneratedForestClockTemplate.rawClock,
      dif_pos hj]
  · simp only [cavityGeneratedFiniteClockLabels, CavityGeneratedConstructedForest.component,
      CavityGeneratedConstructedForest.clockTemplate, CavityGeneratedForestClockTemplate.rawClock,
      dif_neg hj, CavityGeneratedClockLabel.value]

private theorem crossOriginForestOrderIff (W : CavityGeneratedConstructedForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    h ∈ W.clockTemplate.orderSet ↔
      ∀c, h ∈ nativeStreamingGeneratedComponentOrderSet (W.component c) := by
  change (∀c, ∀j : Fin (W.depth c), _ ≤ _) ↔ (∀c, ∀j : Fin (W.depth c), _ ≤ _)
  simp only [crossOriginComponentRawClock]

private theorem crossOriginSelectionClock_eq_chart (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedOriginSelectionClock W c z =
      printedGeneratedOriginChartClock (W.component c)
        (crossOriginPayloadChart (W.component c) z.2) z.1 (crossOriginFreeClock (W.component c) z.2) := by
  have he : W.clockTemplate.clock z.1 c = nativeStreamingGeneratedComponentClock (W.component c) z.1 :=
    by
      apply congrArg cavityGeneratedClippedClock
      funext j
      change (if hj : j ≤ W.depth c then (W.label c ⟨j, by omega⟩).value z.1 else 0) =
        (cavityGeneratedFiniteClockLabels (W.component c).label j).value z.1
      by_cases hj : j ≤ W.depth c
      · simp only [cavityGeneratedFiniteClockLabels, CavityGeneratedConstructedForest.component, dif_pos hj]
      · simp only [cavityGeneratedFiniteClockLabels, CavityGeneratedConstructedForest.component,
          dif_neg hj, CavityGeneratedClockLabel.value]
  rcases z with ⟨h,g⟩
  rcases g with i | (i | u) <;>
    simp only [cavityGeneratedOriginSelectionClock, cavityGeneratedOriginSelectionOrigin,
      nativeStreamingOriginLevel, crossOriginPayloadChart, crossOriginFreeClock,
      printedGeneratedOriginChartClock, printedGeneratedOriginChartFork, printedGeneratedOriginChartEdge, he] <;> rfl

theorem cavityGeneratedCrossOriginChartForest_append_order (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c))
    (k : NativeStreamingGeneratedCrossEdgeChart) (z : CavityGeneratedCrossOriginPayload W c)
    (hz : z ∈ cavityGeneratedCrossOriginChartEvent W c γ₁ γ₂ k) :
    cavityGeneratedCrossOriginAppend W c z ∈
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).clockTemplate.orderSet := by
  classical
  let H := cavityGeneratedCrossOriginAppend W c z
  have ho : H ∈ (W.reindex (fun i => i.castSucc.castSucc)).clockTemplate.orderSet := by
    rw [W.reindex_orderSet]
    simpa only [Set.mem_preimage, Function.comp_def, H, cavityGeneratedCrossOriginAppend,
      Fin.snoc_castSucc] using hz.1.2.1
  apply (crossOriginForestOrderIff _ H).mpr
  intro d
  by_cases hd : d = c
  · subst d
    rw [cavityGeneratedCrossOriginChartForest_same]
    have ht₁ : cavityGeneratedOriginSelectionClock W c z.1 =
        printedGeneratedOriginChartClock (W.component c) γ₁ z.1.1
          (crossOriginFreeClock (W.component c) z.1.2) := by
      rw [crossOriginSelectionClock_eq_chart, hz.1.1]
    have ht₂ : cavityGeneratedOriginSecondSelectionClock W c z =
        printedGeneratedOriginChartClock (W.component c) γ₂ z.1.1
          (crossOriginFreeClock (W.component c) z.2) := by
      change cavityGeneratedOriginSelectionClock W c (z.1.1, z.2) = _
      rw [crossOriginSelectionClock_eq_chart, hz.2.1.1]
    have hc := printedGeneratedOriginCrossChartComponent_order (W.component c) γ₁ γ₂ k z.1.1
      (crossOriginFreeClock (W.component c) z.1.2) (crossOriginFreeClock (W.component c) z.2)
      ((crossOriginForestOrderIff W z.1.1).mp hz.1.2.1 c) hz.1.2.2 hz.2.1.2.2
      (crossOriginChartActive_structural _ γ₁ γ₂ k _ _ hz.2.2)
    simpa only [H, cavityGeneratedCrossOriginAppend, ht₁, ht₂,
      printedGeneratedOriginCrossChartAppend] using hc
  · rw [cavityGeneratedCrossOriginChartForest_other W c γ₁ γ₂ k d hd]
    exact (crossOriginForestOrderIff _ H).mp ho d

def cavityGeneratedCrossOriginChartMeasure (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+2)) :=
  (((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
      (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst).restrict
    (cavityGeneratedCrossOriginChartEvent W c γ₁ γ₂ k)).map (cavityGeneratedCrossOriginAppend W c)

theorem cavityGeneratedCrossOriginChartMeasure_order (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart) :
    ∀ᵐh ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ₁ γ₂ k,
      h ∈ (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).clockTemplate.orderSet := by
  unfold cavityGeneratedCrossOriginChartMeasure
  apply (ae_map_iff (measurable_cavityGeneratedCrossOriginAppend W c).aemeasurable
    (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).clockTemplate.isClosed_orderSet.measurableSet).mpr
  exact (ae_restrict_mem (measurableSet_cavityGeneratedCrossOriginChartEvent W c γ₁ γ₂ k)).mono
    (fun z hz => cavityGeneratedCrossOriginChartForest_append_order W c γ₁ γ₂ k z hz)

theorem cavityGeneratedCrossOriginChartMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedCrossOriginChartMeasure μ a W c M γ₁ γ₂ k) cavityGeneratedHistoryMarks
      ((((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))^2)*C) := by
  let κ := cavityGeneratedOriginSelectionKernel μ a W c
  let N := (M ⊗ₘ κ) ⊗ₘ κ.comap Prod.fst measurable_fst
  let marks := cavityGeneratedPayloadExtendedMarks
    (cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks
      (cavityGeneratedOriginSelectionClock W c)) (cavityGeneratedOriginSecondSelectionClock W c)
  have hm : ∀i, Measurable (marks i) :=
    cavityGeneratedPayloadExtendedMarks_measurable _
      (cavityGeneratedPayloadExtendedMarks_measurable _ cavityGeneratedHistoryMarks_measurable _
        (measurable_cavityGeneratedOriginSelectionClock W c)) _
      (measurable_cavityGeneratedOriginSecondSelectionClock W c)
  have hb := cavityGeneratedOriginDoubleSelection_payload_budget μ a ha hμ W c M C hM horder
  have hr := cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) marks hm _ hb
    (Measure.restrict_le_self (s := cavityGeneratedCrossOriginChartEvent W c γ₁ γ₂ k) (μ := N))
  apply cavityGeneratedMarkBudget_map (parisiFreeMeasure μ a) _ marks cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _ hr (cavityGeneratedCrossOriginAppend W c)
    (measurable_cavityGeneratedCrossOriginAppend W c)
  intro i
  funext z
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, cavityGeneratedHistoryMarks, cavityGeneratedCrossOriginAppend,
      marks, cavityGeneratedPayloadExtendedMarks, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, cavityGeneratedHistoryMarks, cavityGeneratedCrossOriginAppend,
        marks, cavityGeneratedPayloadExtendedMarks, Fin.snoc_last, Fin.snoc_castSucc]
    · simp only [Function.comp_apply, cavityGeneratedHistoryMarks, cavityGeneratedCrossOriginAppend,
        marks, cavityGeneratedPayloadExtendedMarks, Fin.snoc_last, Fin.snoc_castSucc]

end QuantitativeFollowup
