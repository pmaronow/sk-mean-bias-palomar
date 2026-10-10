module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossForestReceiver
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossMeasurable
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossChartCoverage

@[expose] public section

/-! Real chart-restricted double-original selections transport the whole
old forest observable into the computed cross successor. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem cavityGeneratedObservedRawCross_cross_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
    (hl : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l)
    (hk : cavityGeneratedRawCrossChartHolds (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
      (cavityGeneratedRawCrossSite (W.tree c) δ) k r l) :
    (∫σ,nativeStreamingPatternMoment D μ a (W.clock h c) (W.tree c)
      (fun τ=>F (h,Function.update σ c τ))
      (.cross (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
        (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) : Measure _))=
      cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ k F (cavityGeneratedRawCrossAppend h r l) := by
  let G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1)×Configuration (n+1)) → ℝ :=
    fun z=>F (h,z.1)*cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (W.clock h c) (W.tree c)
        (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
        (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l)) z.2.1 z.2.2
  have hp := cavityGeneratedObservedRawCross_terminal_receiver D μ a W c γ δ k h r l hr hl hk G
  refine hp.trans ?_
  apply integral_congr_ae
  exact .of_forall fun σ=>(cavityGeneratedObservedRawCrossTest_eq_source W c γ δ k F h r l hr hl hk σ).symm

private theorem selectedOrigin_chartClock
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedRawCrossOrigin (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
      (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g))=
      cavityGeneratedOriginSelectionOrigin (W.tree c) g := by
  rcases g with i | (z | u) <;> rfl

private theorem selectedCell_chartClock
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection (W.tree c))
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

def cavityGeneratedObservedRawCrossSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedObservedRawCrossPayload W c) : ℝ :=
  ∫σ,nativeStreamingPatternMoment D μ a (W.clock z.1.1 c) (W.tree c)
    (fun τ=>F (z.1.1,Function.update σ c τ))
    (.cross (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2)
      (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1.1) : Measure _)

theorem cavityGeneratedObservedRawCross_source_event_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedObservedRawCrossPayload W c)
    (hz : z∈cavityGeneratedObservedRawCrossChartEvent W c γ δ k) :
    cavityGeneratedObservedRawCrossSourceValue D μ a W c F z=
      cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ k F
        (cavityGeneratedRawOriginDoubleAppendedHistory (fun h=>W.clock h c) (W.tree c) z) := by
  rcases z with ⟨⟨h,g⟩,g'⟩
  rcases (cavityGeneratedObservedRawCrossChartEvent_iff W c γ δ k ((h,g),g')).mp hz with
    ⟨⟨hγ,_,hr⟩,⟨hδ,_,hl⟩,hk⟩
  subst γ
  subst δ
  have hc : cavityGeneratedRawCrossChartHolds (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g')) k
      (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g))
      (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g')) := by
    rcases g with i | (z | u) <;> rcases g' with j | (z' | v)
    all_goals first | exact hk | trivial
  have H := cavityGeneratedObservedRawCross_cross_receiver D μ a W c
    (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g)
    (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g') k F h _ _
    (selectedCell_chartClock W c h g hr) (selectedCell_chartClock W c h g' hl) hc
  rw [selectedOrigin_chartClock,selectedOrigin_chartClock] at H
  exact H

end QuantitativeFollowup
