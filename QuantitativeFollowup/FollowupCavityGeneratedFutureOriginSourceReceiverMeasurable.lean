module
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiverForest

@[expose] public section

/-! The genuine enlarged forest callback is jointly measurable for an
arbitrary measurable old-history/old-terminal test. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def cavityGeneratedFutureOriginTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) : ℝ :=
  let z := cavityGeneratedFutureOriginTerminalProjection W c γ j σ
  F (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H),z.1) *
    cavitySpinOverlapDefect n (H (Fin.last (m+1))) z.2.1 z.2.2

theorem measurable_cavityGeneratedFutureOriginTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+2) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedFutureOriginChartForest W c γ j).depth
        (cavityGeneratedFutureOriginChartForest W c γ j).tree =>
      cavityGeneratedFutureOriginTest W c γ j F z.1 z.2) := by
  classical
  apply measurable_from_prod_countable_left
  intro σ
  let z := cavityGeneratedFutureOriginTerminalProjection W c γ j σ
  have hp : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)) :=
    cavityGeneratedHistoryPrefix_measurable.comp cavityGeneratedHistoryPrefix_measurable
  have hval := hF.comp (hp.prodMk (measurable_const : Measurable (fun _ :
    CavityGeneratedHistory Paper.Overlap (m+2) => z.1)))
  have hclock : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
      H (Fin.last (m+1))) := measurable_pi_apply (Fin.last (m+1))
  change Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2) =>
    F (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H),z.1) *
      cavitySpinOverlapDefect n (H (Fin.last (m+1))) z.2.1 z.2.2)
  exact hval.mul (measurable_const.sub
    (((measurable_subtype_coe.comp hclock).mul_const _).mul_const _))

def cavityGeneratedFutureOriginExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℝ :=
  ∫σ,cavityGeneratedFutureOriginTest W c γ j F H σ
    ∂cavityGeneratedForestTerminalKernel D μ a (cavityGeneratedFutureOriginChartForest W c γ j) H

theorem measurable_cavityGeneratedFutureOriginExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (cavityGeneratedFutureOriginExpectation D μ a W c γ j F) :=
  ((measurable_cavityGeneratedFutureOriginTest W c γ j F hF).stronglyMeasurable.integral_kernel_prod_right').measurable

theorem cavityGeneratedFutureOrigin_future_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r)
    (hl : nativeStreamingGeneratedComponentClock (W.component c) h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock (W.component c) h j)
    (hfuture : printedGeneratedOriginChartClock (W.component c) γ h r < l) :
    (∫σ,nativeStreamingPatternMoment D μ a (W.clockTemplate.clock h c) (W.tree c)
      (fun τ=>F (h,Function.update σ c τ))
      (.future (printedGeneratedFutureOriginChartOrigin (W.component c) γ r) j l)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    cavityGeneratedFutureOriginExpectation D μ a W c γ j F
      (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock (W.component c) γ h r) l) := by
  let G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ :=
    fun z=>F (h,z.1)*cavitySpinOverlapDefect n l z.2.1 z.2.2
  have hp := cavityGeneratedFutureOrigin_terminal_receiver D μ a W c γ j h r l hh hr hl hfuture G
  simpa only [G,nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,
    nativeStreamingDefectSpinTest,cavityGeneratedFutureOriginExpectation,cavityGeneratedFutureOriginTest,
    cavityGeneratedForestTerminalKernel_apply,nativeStreamingGeneratedCrossEdgeAppend,
    cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last] using hp

end QuantitativeFollowup
