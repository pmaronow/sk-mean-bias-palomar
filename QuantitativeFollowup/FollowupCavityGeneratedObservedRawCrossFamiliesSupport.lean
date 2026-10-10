module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossChartCoverage

@[expose] public section

/-! Honest source-chart restriction transports both original selections
into the computed raw successor support. The graph appends their actual
physical levels, including retained vertices and the original root. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

private theorem rawCross_selected_cell (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (g : CavityGeneratedOriginSelection (W.tree c))
    (hg : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
      (cavityGeneratedObservedRawCrossFreeClock (W.tree c) g)) :
    cavityGeneratedRawCrossCell (W.clock h c) (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
      (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g)) := by
  rcases g with i | (z | u)
  · trivial
  · exact hg
  · trivial

private theorem rawCross_selected_level (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (g : CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g)=
      nativeStreamingOriginLevel (W.clock h c)
        (cavityGeneratedRawCrossOrigin (W.tree c)
          (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
          (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g))) := by
  rcases g with i | (z | u) <;> rfl

theorem cavityGeneratedObservedRawCrossChartEvent_append_support
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (z : CavityGeneratedObservedRawCrossPayload W c)
    (hz : z∈cavityGeneratedObservedRawCrossChartEvent W c γ δ k) :
    cavityGeneratedRawOriginDoubleAppendedHistory (fun h=>W.clock h c) (W.tree c) z∈
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).supportSet := by
  rcases z with ⟨⟨h,g⟩,g'⟩
  have hh := (cavityGeneratedObservedRawCrossChartEvent_iff W c γ δ k ((h,g),g')).mp hz
  rcases hh with ⟨⟨hγ,hh,hr⟩,⟨hδ,_,hl⟩,hk⟩
  subst γ
  subst δ
  have hchosen : cavityGeneratedRawCrossChartHolds (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g')) k
      (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g))
      (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g')) := by
    rcases g with i | (z | u) <;> rcases g' with j | (z' | v)
    all_goals first | exact hk | trivial
  exact cavityGeneratedObservedRawCrossChartForest_support_append W c
    (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g)
    (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g') k h hh _ _
    (rawCross_selected_cell W c h g hr) (rawCross_selected_cell W c h g' hl) hchosen
    (rawCross_selected_level W c h g) (rawCross_selected_level W c h g')

theorem cavityGeneratedObservedRawCrossChartMeasure_support
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    ∀ᵐH ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ k M,
      H∈(cavityGeneratedObservedRawCrossChartForest W c γ δ k).supportSet := by
  unfold cavityGeneratedObservedRawCrossChartMeasure cavityGeneratedRawOriginCrossSourceMeasure
  apply (ae_map_iff (measurable_cavityGeneratedRawOriginDoubleAppendedHistory
    (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).aemeasurable
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).measurableSet_supportSet).mpr
  exact (ae_restrict_mem (measurableSet_cavityGeneratedObservedRawCrossChartEvent W c γ δ k)).mono
    fun z hz=>cavityGeneratedObservedRawCrossChartEvent_append_support W c γ δ k z hz

end QuantitativeFollowup
