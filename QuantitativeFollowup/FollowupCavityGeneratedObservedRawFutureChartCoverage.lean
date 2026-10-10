module
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedRawOriginCellSupport
public import FourPapersCommon.FiniteMeasureChartPartition

@[expose] public section

/-! The future charts partition the original selected payload and a genuinely
independent free clock. Distinct halfclosed future cells are disjoint, so their
aggregate budget is charged once before applying the origin bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedObservedRawFutureCellEvent (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (j : Fin (W.depth c)) :
    Set ((CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) :=
  {z | z.2 ∈ Ioc (W.clock z.1.1 c (j+1)) (W.clock z.1.1 c j) ∧
    cavityGeneratedRawOriginSelectionClock (fun h => W.clock h c) (W.tree c) z.1 < z.2}

theorem measurableSet_cavityGeneratedObservedRawFutureCellEvent
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (j : Fin (W.depth c)) :
    MeasurableSet (cavityGeneratedObservedRawFutureCellEvent W c j) := by
  have hq (k : ℕ) : Measurable (fun z :
      (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
        Paper.Overlap => W.clock z.1.1 c k) := (W.measurable_clock c k).comp measurable_fst.fst
  have hr : Measurable (fun z :
      (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
        Paper.Overlap => cavityGeneratedRawOriginSelectionClock
          (fun h => W.clock h c) (W.tree c) z.1) := (measurable_cavityGeneratedRawOriginSelectionClock
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c)).comp measurable_fst
  have hqr (k : ℕ) := measurable_subtype_coe.comp (hq k)
  have hrr := measurable_subtype_coe.comp hr
  have hlr : Measurable (fun z :
      (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
        Paper.Overlap => (z.2 : ℝ)) := measurable_subtype_coe.comp measurable_snd
  exact ((measurableSet_lt (hqr (j+1)) hlr).inter
    (measurableSet_le hlr (hqr j))).inter (measurableSet_lt hrr hlr)

private theorem rawFuture_cell_of_valid (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection U.tree)
    (l : Paper.Overlap) (j : Fin U.depth)
    (hg : cavityGeneratedOriginCellValid (U.clock h) U.tree
      (cavityGeneratedOriginSelectionOrigin U.tree g)) :
    cavityGeneratedObservedRawFutureSourceCell (U.clock h) U.tree
      (cavityGeneratedObservedRawFuturePayloadChart U.tree g) j
      (cavityGeneratedRawOriginSelectionClock (fun h => U.clock h) U.tree (h,g)) l ↔
      l ∈ Ioc (U.clock h (j+1)) (U.clock h j) ∧
        cavityGeneratedRawOriginSelectionClock (fun h => U.clock h) U.tree (h,g) < l := by
  rcases g with i | (z | u)
  · simp only [cavityGeneratedObservedRawFutureSourceCell,
      cavityGeneratedObservedRawFuturePayloadChart,cavityGeneratedObservedRawFutureOrigin,
      cavityGeneratedRawOriginSelectionClock,cavityGeneratedOriginSelectionOrigin,
      nativeStreamingOriginLevel,true_and,eq_self]
  · simp only [cavityGeneratedObservedRawFutureSourceCell,
      cavityGeneratedObservedRawFuturePayloadChart,cavityGeneratedObservedRawFutureOrigin,
      cavityGeneratedRawOriginSelectionClock,cavityGeneratedOriginSelectionOrigin,
      nativeStreamingOriginLevel,eq_self,true_and]
    change z.2 ∈ Ioc (U.clock h (((cavityGeneratedOriginEdges U.tree).get z.1).depth+1))
      (U.clock h ((cavityGeneratedOriginEdges U.tree).get z.1).depth) at hg
    simp only [hg,true_and]
  · simp only [cavityGeneratedObservedRawFutureSourceCell,
      cavityGeneratedObservedRawFuturePayloadChart,cavityGeneratedObservedRawFutureOrigin,
      cavityGeneratedRawOriginSelectionClock,cavityGeneratedOriginSelectionOrigin,
      nativeStreamingOriginLevel,true_and,eq_self]

theorem cavityGeneratedObservedRawFutureSourceEvent_iff_of_valid
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) (hs : z.1.1 ∈ W.supportSet)
    (hg : cavityGeneratedOriginCellValid (W.clock z.1.1 c) (W.tree c)
      (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2)) :
    z ∈ cavityGeneratedObservedRawFutureSourceEvent W c γ j ↔
      cavityGeneratedObservedRawFuturePayloadChart (W.tree c) z.1.2 = γ ∧
        z ∈ cavityGeneratedObservedRawFutureCellEvent W c j := by
  unfold cavityGeneratedObservedRawFutureSourceEvent
  simp only [mem_setOf_eq,hs,true_and]
  by_cases he : cavityGeneratedObservedRawFuturePayloadChart (W.tree c) z.1.2 = γ
  · subst γ
    simp only [eq_self,true_and,cavityGeneratedObservedRawFutureComponentEvent,
      mem_setOf_eq,cavityGeneratedObservedRawFutureAppend_prefix]
    have hp : z.1.1 ∈ (W.component c).supportSet := hs c
    simpa only [cavityGeneratedObservedRawFutureAppend_prefix,hp,true_and,
      cavityGeneratedObservedRawFutureAppend,cavityGeneratedRawOriginFutureAppendedHistory,
      cavityGeneratedRawOriginAppendedHistory,cavityGeneratedObservedRawFutureFirstMark,
      cavityGeneratedObservedRawFutureSecondMark,Fin.snoc_castSucc,Fin.snoc_last,
      cavityGeneratedObservedRawFutureCellEvent,mem_setOf_eq,
      CavityGeneratedObservedRawForest.clock,CavityGeneratedObservedRawForest.tree,Prod.eta] using
      rawFuture_cell_of_valid (W.component c) z.1.1 z.1.2 z.2 j hg
  · simp only [he,false_and]

theorem cavityGeneratedObservedRawFutureSourceEvent_subset_cell
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c)) :
    cavityGeneratedObservedRawFutureSourceEvent W c γ j ⊆
      cavityGeneratedObservedRawFutureCellEvent W c j := by
  intro z hz
  have hp := hz.2.2.2.2.2
  rw [cavityGeneratedObservedRawFutureAppend_prefix] at hp
  simpa only [
    cavityGeneratedObservedRawFutureAppend,cavityGeneratedRawOriginFutureAppendedHistory,
    cavityGeneratedRawOriginAppendedHistory,cavityGeneratedObservedRawFutureFirstMark,
    cavityGeneratedObservedRawFutureSecondMark,Fin.snoc_castSucc,Fin.snoc_last,
    cavityGeneratedObservedRawFutureCellEvent,mem_setOf_eq,
    CavityGeneratedObservedRawForest.clock] using hp

theorem cavityGeneratedObservedRawFutureCellEvent_disjoint
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    Pairwise (Disjoint on cavityGeneratedObservedRawFutureCellEvent W c) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro z hj hk
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjk) with h | h
  · have hq := W.clock_antitone z.1.1 c (show (j : ℕ)+1 ≤ k by omega)
    exact (not_lt_of_ge (hk.1.2.trans hq)) hj.1.1
  · have hq := W.clock_antitone z.1.1 c (show (k : ℕ)+1 ≤ j by omega)
    exact (not_lt_of_ge (hj.1.2.trans hq)) hk.1.1

theorem cavityGeneratedObservedRawFutureSourceEvent_disjoint
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    Pairwise (Disjoint on (fun s : CavityGeneratedObservedRawOriginChart (W.tree c) ×
      Fin (W.depth c) => cavityGeneratedObservedRawFutureSourceEvent W c s.1 s.2)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro z hs ht
  have hg : s.1 = t.1 := hs.2.1.symm.trans ht.2.1
  have hj : s.2 ≠ t.2 := by intro he; exact hst (Prod.ext hg he)
  exact Set.disjoint_left.mp (cavityGeneratedObservedRawFutureCellEvent_disjoint W c hj)
    (cavityGeneratedObservedRawFutureSourceEvent_subset_cell W c s.1 s.2 hs)
    (cavityGeneratedObservedRawFutureSourceEvent_subset_cell W c t.1 t.2 ht)

private theorem rawFuture_support_valid_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hs : ∀ᵐh ∂M, h ∈ W.supportSet) :
    ∀ᵐz ∂(M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a),
      z.1.1 ∈ W.supportSet ∧ cavityGeneratedOriginCellValid (W.clock z.1.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2) := by
  have hvalid := cavityGeneratedRawOriginSelectionJointMeasure_ae_cell_valid μ a
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) M
  have hsup := Measure.ae_compProd_of_ae_fst
    (cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c)) W.measurableSet_supportSet hs
  have hm : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) | z.1 ∈ W.supportSet ∧
      cavityGeneratedOriginCellValid (W.clock z.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)} :=
    (W.measurableSet_supportSet.preimage measurable_fst).inter
      (measurableSet_cavityGeneratedRawOriginCellValid _ (W.measurable_clock c) (W.tree c))
  rw [←Measure.compProd_const]
  exact Measure.ae_compProd_of_ae_fst (Kernel.const _ (parisiFreeMeasure μ a)) hm
    (hsup.and hvalid)

theorem cavityGeneratedObservedRawFutureSourceMeasure_sum_charts
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) (j : Fin (W.depth c)) :
    (∑γ, cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) =
      (((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)).restrict
          (cavityGeneratedObservedRawFutureCellEvent W c j)).map
            (cavityGeneratedObservedRawFutureAppend W c) := by
  classical
  let P := (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
    (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)
  have ha := rawFuture_support_valid_ae μ a W c M hsupport
  have hcover : ∀ᵐz ∂P.restrict (cavityGeneratedObservedRawFutureCellEvent W c j),
      ∃γ, z ∈ cavityGeneratedObservedRawFutureSourceEvent W c γ j := by
    filter_upwards [ae_restrict_of_ae ha,ae_restrict_mem
      (measurableSet_cavityGeneratedObservedRawFutureCellEvent W c j)] with z hz hc
    exact ⟨cavityGeneratedObservedRawFuturePayloadChart (W.tree c) z.1.2,
      (cavityGeneratedObservedRawFutureSourceEvent_iff_of_valid W c _ j z hz.1 hz.2).mpr ⟨rfl,hc⟩⟩
  have hd : Pairwise (Disjoint on (fun γ => cavityGeneratedObservedRawFutureSourceEvent W c γ j)) := by
    intro γ δ hne
    exact cavityGeneratedObservedRawFutureSourceEvent_disjoint W c
      (show (γ,j) ≠ (δ,j) by intro he; exact hne (congrArg Prod.fst he))
  have he (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
      P.restrict (cavityGeneratedObservedRawFutureSourceEvent W c γ j) =
        (P.restrict (cavityGeneratedObservedRawFutureCellEvent W c j)).restrict
          (cavityGeneratedObservedRawFutureSourceEvent W c γ j) := by
    rw [Measure.restrict_restrict (measurableSet_cavityGeneratedObservedRawFutureSourceEvent W c γ j)]
    rw [Set.inter_eq_left.mpr (cavityGeneratedObservedRawFutureSourceEvent_subset_cell W c γ j)]
  have hp := finiteMeasureChartPartition_sum_map_restrict
    (P.restrict (cavityGeneratedObservedRawFutureCellEvent W c j))
    (fun γ => cavityGeneratedObservedRawFutureSourceEvent W c γ j)
    (measurableSet_cavityGeneratedObservedRawFutureSourceEvent W c · j) hd hcover
    (cavityGeneratedObservedRawFutureAppend W c) (measurable_cavityGeneratedObservedRawFutureAppend W c)
  simpa only [cavityGeneratedObservedRawFutureSourceMeasure,cavityGeneratedRawOriginFutureSourceMeasure,
    ←he,cavityGeneratedObservedRawFutureAppend,P] using hp

theorem cavityGeneratedObservedRawFutureSourceMeasure_sum_le_full
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    (∑γ, ∑j, cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) ≤
      ((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)).map
          (cavityGeneratedObservedRawFutureAppend W c) := by
  classical
  let P := (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
    (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)
  have hm : (∑s : CavityGeneratedObservedRawOriginChart (W.tree c) × Fin (W.depth c),
      P.restrict (cavityGeneratedObservedRawFutureSourceEvent W c s.1 s.2)) ≤ P := by
    rw [←Measure.sum_fintype,←Measure.restrict_iUnion
      (cavityGeneratedObservedRawFutureSourceEvent_disjoint W c)
      (fun s => measurableSet_cavityGeneratedObservedRawFutureSourceEvent W c s.1 s.2)]
    exact Measure.restrict_le_self
  have hmap := Measure.map_mono hm (measurable_cavityGeneratedObservedRawFutureAppend W c)
  rw [Measure.map_finset_sum' (measurable_cavityGeneratedObservedRawFutureAppend W c).aemeasurable] at hmap
  simpa only [Fintype.sum_prod_type,cavityGeneratedObservedRawFutureSourceMeasure,
    cavityGeneratedRawOriginFutureSourceMeasure,cavityGeneratedObservedRawFutureAppend,P] using hmap

theorem cavityGeneratedObservedRawFutureSourceMeasure_sum_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (∑γ, ∑j, cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M)
      cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*C) := by
  have hb := cavityGeneratedObservedRawOriginFutureSourceMeasure_budget μ a ha hμ W c M C hM hsupport
    Set.univ
  simp only [cavityGeneratedRawOriginFutureSourceMeasure,Measure.restrict_univ] at hb
  exact cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _ hb
    (cavityGeneratedObservedRawFutureSourceMeasure_sum_le_full μ a W c M)

end QuantitativeFollowup
