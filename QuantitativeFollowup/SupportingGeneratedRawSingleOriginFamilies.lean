module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginCharts
public import QuantitativeFollowup.FollowupCavityGeneratedRawSourceMeasures
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawSourceBudgets
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawLeafCounts

@[expose] public section

/-! Genuine raw single/current source families retain the original
selection payload until the one actual selected-clock graph map. Output
support is derived from the original support and its actual source cell. -/
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

def cavityGeneratedObservedRawOriginPayloadChart (U : CavityGeneratedObservedRawComponent m) :
    CavityGeneratedOriginSelection U.tree → CavityGeneratedObservedRawOriginChart U.tree
  | .inl i => .inl i
  | .inr (.inl z) => .inr (.inl z.1)
  | .inr (.inr u) => .inr (.inr u)

theorem measurable_cavityGeneratedObservedRawOriginPayloadChart
    (U : CavityGeneratedObservedRawComponent m) :
    Measurable (cavityGeneratedObservedRawOriginPayloadChart U) := by
  apply measurable_fun_sum
  · exact measurable_inl
  · apply measurable_fun_sum
    · exact (measurable_inr.comp measurable_inl).comp measurable_fst
    · exact measurable_inr.comp measurable_inr

def cavityGeneratedObservedRawOriginPayloadFreeClock (U : CavityGeneratedObservedRawComponent m) :
    CavityGeneratedOriginSelection U.tree → Paper.Overlap
  | .inl _ => 0
  | .inr (.inl z) => z.2
  | .inr (.inr _) => 0

theorem measurable_cavityGeneratedObservedRawOriginPayloadFreeClock
    (U : CavityGeneratedObservedRawComponent m) :
    Measurable (cavityGeneratedObservedRawOriginPayloadFreeClock U) :=
  measurable_const.sumElim (measurable_snd.sumElim measurable_const)

theorem cavityGeneratedObservedRawOriginSelectionClock_eq_chart
    (U : CavityGeneratedObservedRawComponent m)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection U.tree) :
    cavityGeneratedRawOriginSelectionClock U.clock U.tree z =
      cavityGeneratedObservedRawChartClock U (cavityGeneratedObservedRawOriginPayloadChart U z.2)
        z.1 (cavityGeneratedObservedRawOriginPayloadFreeClock U z.2) := by
  rcases z with ⟨h,g⟩
  rcases g with i | (z | u) <;> rfl

theorem cavityGeneratedObservedRawOriginSelectionOrigin_eq_chart
    (U : CavityGeneratedObservedRawComponent m) (g : CavityGeneratedOriginSelection U.tree) :
    cavityGeneratedOriginSelectionOrigin U.tree g =
      cavityGeneratedObservedRawChartOrigin U (cavityGeneratedObservedRawOriginPayloadChart U g)
        (cavityGeneratedObservedRawOriginPayloadFreeClock U g) := by
  rcases g with i | (z | u) <;> rfl

private theorem generatedRawOriginChartSingleton
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree) :
    MeasurableSet ({γ} : Set (CavityGeneratedObservedRawOriginChart U.tree)) := by
  rcases γ with i | (i | u)
  · have hh : MeasurableSet (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginForkVertices U.tree).length)) :
        Set (CavityGeneratedObservedRawOriginChart U.tree)) := (measurableSet_singleton i).inl_image
    simpa only [Set.image_singleton] using hh
  · have hi : MeasurableSet (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginEdges U.tree).length)) :
        Set (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)) := (measurableSet_singleton i).inl_image
    have hh : MeasurableSet (Sum.inr '' (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginEdges U.tree).length))) :
        Set (CavityGeneratedObservedRawOriginChart U.tree)) := hi.inr_image
    simpa only [Set.image_singleton] using hh
  · have hi : MeasurableSet (Sum.inr '' ({u} : Set Unit) :
        Set (Fin (cavityGeneratedOriginEdges U.tree).length ⊕ Unit)) := (measurableSet_singleton u).inr_image
    have hh : MeasurableSet (Sum.inr '' (Sum.inr '' ({u} : Set Unit)) :
        Set (CavityGeneratedObservedRawOriginChart U.tree)) := hi.inr_image
    simpa only [Set.image_singleton] using hh

def cavityGeneratedObservedRawSingleOriginChartEvent
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    Set (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :=
  {z | cavityGeneratedObservedRawOriginPayloadChart (W.component c) z.2 = γ ∧
    z.1∈W.supportSet ∧ cavityGeneratedObservedRawChartCell (W.component c) γ z.1
      (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2)}

theorem measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    MeasurableSet (cavityGeneratedObservedRawSingleOriginChartEvent W c γ) := by
  have hclass := (generatedRawOriginChartSingleton (W.component c) γ).preimage
    ((measurable_cavityGeneratedObservedRawOriginPayloadChart (W.component c)).comp
      (measurable_snd : Measurable (Prod.snd :
        CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) → _)))
  have hold := W.measurableSet_supportSet.preimage
    (measurable_fst : Measurable (Prod.fst :
      CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) → _))
  have hcell : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      cavityGeneratedObservedRawChartCell (W.component c) γ z.1
        (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2)} := by
    rcases γ with i | (i | u)
    · exact MeasurableSet.univ
    · have hr := (measurable_cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c)).comp
        (measurable_snd : Measurable (Prod.snd :
          CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) → _))
      have hq (j : ℕ) := (W.measurable_clock c j).comp
        (measurable_fst : Measurable (Prod.fst :
          CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) → _))
      change MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) |
        (W.clock z.1 c ((cavityGeneratedObservedRawChartEdge (W.component c) i).depth+1):ℝ)≤
          (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2:ℝ) ∧
        (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2:ℝ)≤
          (W.clock z.1 c (cavityGeneratedObservedRawChartEdge (W.component c) i).depth:ℝ)}
      exact (measurableSet_le (measurable_subtype_coe.comp (hq ((cavityGeneratedObservedRawChartEdge (W.component c) i).depth+1)))
        (measurable_subtype_coe.comp hr)).inter
          (measurableSet_le (measurable_subtype_coe.comp hr)
            (measurable_subtype_coe.comp (hq (cavityGeneratedObservedRawChartEdge (W.component c) i).depth)))
    · exact MeasurableSet.univ
  exact hclass.inter (hold.inter hcell)

def cavityGeneratedObservedRawSingleOriginChartForest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedObservedRawForest (m+1) :=
  cavityGeneratedObservedRawForestReplaceComponent (W.reindex Fin.castSucc) c
    (cavityGeneratedObservedRawChartComponent (W.component c) γ k)

def cavityGeneratedObservedRawSingleOriginChartMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+1)) :=
  cavityGeneratedRawOriginSourceMeasure μ a (fun h=>W.clock h c) (W.measurable_clock c)
    (W.tree c) M (cavityGeneratedObservedRawSingleOriginChartEvent W c γ)

theorem cavityGeneratedObservedRawSingleOriginChartForest_leafCount
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind) :
    (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).leafCount=W.leafCount+k.newLeafCount := by
  have he := cavityGeneratedObservedRawForestReplaceComponent_leafCount (W.reindex Fin.castSucc) c
    (cavityGeneratedObservedRawChartComponent (W.component c) γ k)
  have hc := cavityGeneratedObservedRawChartComponent_leafCount (W.component c) γ k
  change (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).leafCount+
    (W.component c).leafCount=W.leafCount+
      (cavityGeneratedObservedRawChartComponent (W.component c) γ k).leafCount at he
  change (cavityGeneratedObservedRawChartComponent (W.component c) γ k).leafCount=
    (W.component c).leafCount+k.newLeafCount at hc
  omega

def cavityGeneratedObservedRawOriginalFreshChartMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+1)) :=
  (2 : ℝ≥0∞) • cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ

def cavityGeneratedObservedRawCurrentChartMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+1)) :=
  (cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ).withDensity
    (fun H=>ENNReal.ofReal (Paper.parisiCDF μ (H (Fin.last m))))

theorem cavityGeneratedObservedRawSingleOriginChartEvent_disjoint
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    Pairwise (Disjoint on (cavityGeneratedObservedRawSingleOriginChartEvent W c)) := by
  intro γ δ hne
  apply Set.disjoint_left.mpr
  intro z hz hδ
  exact hne (hz.1.symm.trans hδ.1)

theorem cavityGeneratedObservedRawSingleOriginChartForest_append_support
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z∈cavityGeneratedObservedRawSingleOriginChartEvent W c γ) :
    cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.tree c) z∈
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).supportSet := by
  classical
  let H := cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.tree c) z
  change ∀s : Fin W.componentCount, H∈
    (Function.update (W.reindex Fin.castSucc).component c
      (cavityGeneratedObservedRawChartComponent (W.component c) γ k) s).supportSet
  intro s
  by_cases hs : s=c
  · subst s
    rw [Function.update_self]
    have hc := cavityGeneratedObservedRawChartComponent_support (W.component c) γ k z.1
      (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) (hz.2.1 c) hz.2.2
    have ht : cavityGeneratedRawOriginSelectionClock (W.component c).clock (W.tree c) z =
        cavityGeneratedObservedRawChartClock (W.component c) γ z.1
          (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) := by
      have he := cavityGeneratedObservedRawOriginSelectionClock_eq_chart (W.component c) z
      have hclass : cavityGeneratedObservedRawOriginPayloadChart (W.component c) z.2=γ := hz.1
      rw [hclass] at he
      exact he
    change Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (W.component c).clock (W.tree c) z)∈
      (cavityGeneratedObservedRawChartComponent (W.component c) γ k).supportSet
    rw [ht]
    exact hc
  · rw [Function.update_of_ne hs]
    change (fun i=>H i.castSucc)∈(W.component s).supportSet
    simpa only [H,cavityGeneratedRawOriginAppendedHistory,Fin.snoc_castSucc] using hz.2.1 s

theorem cavityGeneratedObservedRawSingleOriginChartMeasure_support
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind) :
    ∀ᵐH ∂cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ,
      H∈(cavityGeneratedObservedRawSingleOriginChartForest W c γ k).supportSet := by
  unfold cavityGeneratedObservedRawSingleOriginChartMeasure cavityGeneratedRawOriginSourceMeasure
  apply (ae_map_iff (measurable_cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c)
    (W.measurable_clock c) (W.tree c)).aemeasurable
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).measurableSet_supportSet).mpr
  exact (ae_restrict_mem (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ)).mono
    (fun z hz=>cavityGeneratedObservedRawSingleOriginChartForest_append_support W c γ k z hz)

theorem cavityGeneratedObservedRawOriginalFreshChartMeasure_support
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    ∀ᵐH ∂cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ,
      H∈(cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).supportSet :=
  Measure.ae_smul_measure (cavityGeneratedObservedRawSingleOriginChartMeasure_support μ a W c M γ .single) 2

theorem cavityGeneratedObservedRawCurrentChartMeasure_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ≤
      cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ := by
  unfold cavityGeneratedObservedRawCurrentChartMeasure
  simpa only [one_smul] using cavityGenerated_withDensity_le
    (cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ)
    (fun H=>ENNReal.ofReal (Paper.parisiCDF μ (H (Fin.last m)))) 1
    (fun H=>(ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ _)).trans_eq (by norm_num))

theorem cavityGeneratedObservedRawCurrentChartMeasure_support
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    ∀ᵐH ∂cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ,
      H∈(cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).supportSet :=
  (cavityGeneratedObservedRawSingleOriginChartMeasure_support μ a W c M γ .current).filter_mono
    (ae_mono (cavityGeneratedObservedRawCurrentChartMeasure_le μ a W c M γ))

end QuantitativeFollowup
