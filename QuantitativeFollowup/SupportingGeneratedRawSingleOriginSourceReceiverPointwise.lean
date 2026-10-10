module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginSourceReceiverDefinitions

@[expose] public section

/-! A single-origin component receiver is the genuine enlarged forest
expectation, for an arbitrary joint old-terminal test. The redundant old
selected coordinate is integrated out by the actual finite-Pi replacement
law, while all untouched trees remain jointly present. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedObservedRawSingleOrigin_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell (W.component c) γ h r)
    (G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      k.Mark (Configuration (n+1)) → ℝ) :
    (∫ σ, nativeStreamingTerminalMarkMoment
      (printedGeneratedOriginKindProbability D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedObservedRawChartOrigin (W.component c) γ r) k)
      (fun z => G (Function.update σ c z.1,z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    ∫ σ, G (cavityGeneratedObservedRawSingleOriginTerminalProjection W c γ k σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).depth
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree
        ((cavityGeneratedObservedRawSingleOriginChartForest W c γ k).clock
          (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r))) :
        Measure (CavityGeneratedForestTerminalSample (n:=n)
          (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).depth
          (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree)) := by
  let V := W.reindex Fin.castSucc
  let U := cavityGeneratedObservedRawChartComponent (W.component c) γ k
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)
  have hp := integral_cavityGeneratedObservedRawForest_component_replacement D μ a V c U H
    (fun σ => G (cavityGeneratedObservedRawSingleOriginTerminalProjection W c γ k σ))
  change (∫σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree,
    ∫τ : CavityGeneratedObservedRawComponentTerminal n U,
      G (cavityGeneratedObservedRawSingleOriginTerminalProjection W c γ k
        (cavityGeneratedObservedRawForestReplacementTerminal V c U σ τ))
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a U H
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      ((W.reindex Fin.castSucc).clock
        (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r))) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) = _ at hp
  rw [cavityGeneratedObservedRawSingleOrigin_reindexed_terminal_law] at hp
  refine Eq.trans ?_ hp
  apply integral_congr_ae
  refine .of_forall fun σ => ?_
  have hl := cavityGeneratedObservedRawChart_terminal_receiver D μ a (W.component c) γ k h r hr
    (fun z => G (Function.update σ c z.1,z.2))
  refine hl.symm.trans ?_
  apply integral_congr_ae
  exact .of_forall fun τ =>
    (congrArg G (cavityGeneratedObservedRawSingleOriginTerminalProjection_replacement W c γ k σ τ)).symm

theorem cavityGeneratedObservedRawSingleOrigin_originalFresh_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c))
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell (W.component c) γ h r) :
    (∫ σ, nativeStreamingPatternMoment D μ a (W.clock h c) (W.tree c)
      (fun τ => F (h,Function.update σ c τ))
      (.originalFresh i (cavityGeneratedObservedRawChartOrigin (W.component c) γ r))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    ∫ σ, cavityGeneratedObservedRawSingleOriginOriginalFreshTest W c γ F i
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).depth
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).tree
        ((cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).clock
          (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r))) :
        Measure (CavityGeneratedForestTerminalSample (n:=n)
          (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).depth
          (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).tree)) := by
  classical
  let G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree × Configuration (n+1) → ℝ :=
    fun z => F (h,z.1) * cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (W.clock h c) (W.tree c)
        (.vertex (observationLeafVertex (W.tree c) i))
        (cavityGeneratedObservedRawChartOrigin (W.component c) γ r))
      (observationTerminalSpin (W.tree c) i (z.1 c)) z.2
  have hp := cavityGeneratedObservedRawSingleOrigin_terminal_receiver D μ a W c γ .single h r hr G
  simpa only [G,nativeStreamingPatternMoment,printedGeneratedOriginKindProbability,
    nativeStreamingTerminalMarkMoment,nativeStreamingOriginalFreshSpinTest,Function.update_self,
    cavityGeneratedObservedRawSingleOriginOriginalFreshTest,cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last,
    cavityGeneratedObservedRawChartOrigin_clock] using hp

theorem cavityGeneratedObservedRawSingleOrigin_current_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell (W.component c) γ h r) :
    (∫ σ, nativeStreamingPatternMoment D μ a (W.clock h c) (W.tree c)
      (fun τ => F (h,Function.update σ c τ))
      (.current (cavityGeneratedObservedRawChartOrigin (W.component c) γ r))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    ∫ σ, cavityGeneratedObservedRawSingleOriginCurrentTest W c γ F
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).depth
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).tree
        ((cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).clock
          (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r))) :
        Measure (CavityGeneratedForestTerminalSample (n:=n)
          (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).depth
          (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).tree)) := by
  let G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ :=
    fun z => F (h,z.1) * cavitySpinOverlapDefect n
      (nativeStreamingOriginLevel (W.clock h c)
        (cavityGeneratedObservedRawChartOrigin (W.component c) γ r)) z.2.1 z.2.2
  have hp := cavityGeneratedObservedRawSingleOrigin_terminal_receiver D μ a W c γ .current h r hr G
  simpa only [G,nativeStreamingPatternMoment,printedGeneratedOriginKindProbability,
    nativeStreamingTerminalMarkMoment,nativeStreamingDefectSpinTest,
    cavityGeneratedObservedRawSingleOriginCurrentTest,cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last,
    cavityGeneratedObservedRawChartOrigin_clock] using hp

end QuantitativeFollowup
