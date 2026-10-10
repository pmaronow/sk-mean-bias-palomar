module
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginSourceReceiverDefinitions

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

theorem cavityGeneratedSingleOrigin_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r)
    (G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      k.Mark (Configuration (n+1)) → ℝ) :
    (∫ σ, nativeStreamingTerminalMarkMoment
      (printedGeneratedOriginKindProbability D μ a (W.clockTemplate.clock h c) (W.tree c)
        (printedGeneratedOriginChartOrigin (W.component c) γ r) k)
      (fun z => G (Function.update σ c z.1,z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    ∫ σ, G (cavityGeneratedSingleOriginTerminalProjection W c γ k σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedSingleOriginChartForest W c γ k).depth
        (cavityGeneratedSingleOriginChartForest W c γ k).tree
        ((cavityGeneratedSingleOriginChartForest W c γ k).clockTemplate.clock
          (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r))) :
        Measure (CavityGeneratedForestTerminalSample (n:=n)
          (cavityGeneratedSingleOriginChartForest W c γ k).depth
          (cavityGeneratedSingleOriginChartForest W c γ k).tree)) := by
  let V := W.reindex Fin.castSucc
  let U := printedGeneratedOriginChartComponent (W.component c) γ k
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)
  have hp := integral_cavityGeneratedForest_component_replacement D μ a V c U H
    (fun σ => G (cavityGeneratedSingleOriginTerminalProjection W c γ k σ))
  change (∫σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree,
    ∫τ : CavityGeneratedComponentTerminal n U,
      G (cavityGeneratedSingleOriginTerminalProjection W c γ k
        (cavityGeneratedForestReplacementTerminal V c U σ τ))
      ∂cavityGeneratedComponentTerminalMeasure D μ a U H
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      ((W.reindex Fin.castSucc).clockTemplate.clock
        (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r))) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) = _ at hp
  rw [cavityGeneratedSingleOrigin_reindexed_terminal_law] at hp
  refine Eq.trans ?_ hp
  apply integral_congr_ae
  refine .of_forall fun σ => ?_
  have hhU := (cavityGeneratedForest_orderSet_iff_components W h).mp hh c
  have hc : W.clockTemplate.clock h c = nativeStreamingGeneratedComponentClock (W.component c) h :=
    printedGeneratedComponentClock_eq_native (W.component c) h
  have hl := printedGeneratedOriginChart_terminal_receiver D μ a (W.component c) γ k h r hhU hr
    (fun z => G (Function.update σ c z.1,z.2))
  rw [←hc] at hl
  refine hl.symm.trans ?_
  apply integral_congr_ae
  exact .of_forall fun τ =>
    (congrArg G (cavityGeneratedSingleOriginTerminalProjection_replacement W c γ k σ τ)).symm

theorem cavityGeneratedSingleOrigin_originalFresh_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c))
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r) :
    (∫ σ, nativeStreamingPatternMoment D μ a (W.clockTemplate.clock h c) (W.tree c)
      (fun τ => F (h,Function.update σ c τ))
      (.originalFresh i (printedGeneratedOriginChartOrigin (W.component c) γ r))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    ∫ σ, cavityGeneratedSingleOriginOriginalFreshTest W c γ F i
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedSingleOriginChartForest W c γ .single).depth
        (cavityGeneratedSingleOriginChartForest W c γ .single).tree
        ((cavityGeneratedSingleOriginChartForest W c γ .single).clockTemplate.clock
          (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r))) :
        Measure (CavityGeneratedForestTerminalSample (n:=n)
          (cavityGeneratedSingleOriginChartForest W c γ .single).depth
          (cavityGeneratedSingleOriginChartForest W c γ .single).tree)) := by
  classical
  let G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree × Configuration (n+1) → ℝ :=
    fun z => F (h,z.1) * cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (W.clockTemplate.clock h c) (W.tree c)
        (.vertex (observationLeafVertex (W.tree c) i))
        (printedGeneratedOriginChartOrigin (W.component c) γ r))
      (observationTerminalSpin (W.tree c) i (z.1 c)) z.2
  have hp := cavityGeneratedSingleOrigin_terminal_receiver D μ a W c γ .single h r hh hr G
  simpa only [G,nativeStreamingPatternMoment,printedGeneratedOriginKindProbability,
    nativeStreamingTerminalMarkMoment,nativeStreamingOriginalFreshSpinTest,Function.update_self,
    cavityGeneratedSingleOriginOriginalFreshTest,cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last,
    cavityGeneratedOriginChartOrigin_clock] using hp

theorem cavityGeneratedSingleOrigin_current_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r) :
    (∫ σ, nativeStreamingPatternMoment D μ a (W.clockTemplate.clock h c) (W.tree c)
      (fun τ => F (h,Function.update σ c τ))
      (.current (printedGeneratedOriginChartOrigin (W.component c) γ r))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    ∫ σ, cavityGeneratedSingleOriginCurrentTest W c γ F
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedSingleOriginChartForest W c γ .current).depth
        (cavityGeneratedSingleOriginChartForest W c γ .current).tree
        ((cavityGeneratedSingleOriginChartForest W c γ .current).clockTemplate.clock
          (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r))) :
        Measure (CavityGeneratedForestTerminalSample (n:=n)
          (cavityGeneratedSingleOriginChartForest W c γ .current).depth
          (cavityGeneratedSingleOriginChartForest W c γ .current).tree)) := by
  let G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ :=
    fun z => F (h,z.1) * cavitySpinOverlapDefect n
      (nativeStreamingOriginLevel (W.clockTemplate.clock h c)
        (printedGeneratedOriginChartOrigin (W.component c) γ r)) z.2.1 z.2.2
  have hp := cavityGeneratedSingleOrigin_terminal_receiver D μ a W c γ .current h r hh hr G
  simpa only [G,nativeStreamingPatternMoment,printedGeneratedOriginKindProbability,
    nativeStreamingTerminalMarkMoment,nativeStreamingDefectSpinTest,
    cavityGeneratedSingleOriginCurrentTest,cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last,
    cavityGeneratedOriginChartOrigin_clock] using hp

end QuantitativeFollowup
