module
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiverMeasurable

@[expose] public section

/-! Exact future chart integrals use the genuine selected-origin payload,
then one independent free draw in its original halfclosed future cell.
The arbitrary joint old-forest observable keeps the original prefix. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def printedGeneratedFuturePayloadChart (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedOriginSelection U.tree → PrintedGeneratedOriginChart U
  | .inl i => .inl i
  | .inr (.inl z) => .inr (.inl z.1)
  | .inr (.inr u) => .inr (.inr u)

def printedGeneratedFuturePayloadFreeClock (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedOriginSelection U.tree → Paper.Overlap
  | .inl _ => 0
  | .inr (.inl z) => z.2
  | .inr (.inr _) => 0

theorem printedGeneratedFutureSelectionOrigin_eq_chart
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (g : CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedOriginSelectionOrigin (W.tree c) g =
      printedGeneratedFutureOriginChartOrigin (W.component c)
        (printedGeneratedFuturePayloadChart (W.component c) g)
        (printedGeneratedFuturePayloadFreeClock (W.component c) g) := by
  rcases g with i | (i | u) <;> rfl

theorem printedGeneratedFutureSelectionClock_eq_chart
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedOriginSelectionClock W c z =
      printedGeneratedOriginChartClock (W.component c)
        (printedGeneratedFuturePayloadChart (W.component c) z.2) z.1
        (printedGeneratedFuturePayloadFreeClock (W.component c) z.2) := by
  have he : W.clockTemplate.clock z.1 c =
      nativeStreamingGeneratedComponentClock (W.component c) z.1 :=
    printedGeneratedComponentClock_eq_native (W.component c) z.1
  rcases z with ⟨h,g⟩
  rcases g with i | (i | u) <;>
    simp only [cavityGeneratedOriginSelectionClock,cavityGeneratedOriginSelectionOrigin,
      nativeStreamingOriginLevel,printedGeneratedFuturePayloadChart,printedGeneratedFuturePayloadFreeClock,
      printedGeneratedOriginChartClock,printedGeneratedOriginChartFork,
      printedGeneratedOriginChartEdge,he] <;> rfl

theorem cavityGeneratedFutureOrigin_source_event_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z∈cavityGeneratedFutureOriginChartSourceEvent W c γ j) :
    (∫σ,nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1.1 c) (W.tree c)
      (fun τ=>F (z.1.1,Function.update σ c τ))
      (.future (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2) j z.2)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock z.1.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    cavityGeneratedFutureOriginExpectation D μ a W c γ j F
      (cavityGeneratedFutureOriginChartAppend W c z) := by
  have hγ : printedGeneratedFuturePayloadChart (W.component c) z.1.2 = γ := hz.1.1
  have ho : cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2 =
      printedGeneratedFutureOriginChartOrigin (W.component c) γ
        (printedGeneratedFuturePayloadFreeClock (W.component c) z.1.2) := by
    rw [printedGeneratedFutureSelectionOrigin_eq_chart,hγ]
  have ht : cavityGeneratedOriginSelectionClock W c z.1 =
      printedGeneratedOriginChartClock (W.component c) γ z.1.1
        (printedGeneratedFuturePayloadFreeClock (W.component c) z.1.2) := by
    rw [printedGeneratedFutureSelectionClock_eq_chart,hγ]
  unfold cavityGeneratedFutureOriginChartAppend
  rw [ho,ht]
  exact cavityGeneratedFutureOrigin_future_receiver D μ a W c γ j F z.1.1
    (printedGeneratedFuturePayloadFreeClock (W.component c) z.1.2) z.2 hz.1.2.1 hz.1.2.2.1
      hz.1.2.2.2.1 (by simpa only [ht] using hz.1.2.2.2.2)

theorem cavityGeneratedFutureOrigin_source_chart_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    (∫H,cavityGeneratedFutureOriginExpectation D μ a W c γ j F H
      ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j) =
    ∫z,(∫σ,nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1.1 c) (W.tree c)
      (fun τ=>F (z.1.1,Function.update σ c τ))
      (.future (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2) j z.2)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock z.1.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
        Kernel.const _ (parisiFreeMeasure μ a)).restrict
          (cavityGeneratedFutureOriginChartSourceEvent W c γ j) := by
  rw [cavityGeneratedFutureOriginChartSourceMeasure,integral_map
    (measurable_cavityGeneratedFutureOriginChartAppend W c).aemeasurable
    (measurable_cavityGeneratedFutureOriginExpectation D μ a W c γ j F hF).aestronglyMeasurable]
  apply integral_congr_ae
  exact (ae_restrict_mem (measurableSet_cavityGeneratedFutureOriginChartSourceEvent W c γ j)).mono
    (fun z hz=>(cavityGeneratedFutureOrigin_source_event_receiver D μ a W c γ j F z hz).symm)

end QuantitativeFollowup
