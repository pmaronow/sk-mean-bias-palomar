module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossForestProjection
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossTerminalReceiver

@[expose] public section

/-! Exact replacement transports a joint old-forest terminal test through
both original chosen locations and the ordered fresh continuation pair. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem cavityGeneratedObservedRawCross_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
    (hl : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l)
    (hk : cavityGeneratedRawCrossChartHolds (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
      (cavityGeneratedRawCrossSite (W.tree c) δ) k r l)
    (G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1)×Configuration (n+1)) → ℝ) :
    (∫σ,nativeStreamingTerminalMarkMoment
      (nativeStreamingOriginCrossProbability D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
        (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l))
      (fun z=>G (Function.update σ c z.1,z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) : Measure _))=
    ∫σ,G (cavityGeneratedObservedRawCrossTerminalProjection W c γ δ k σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree
        ((cavityGeneratedObservedRawCrossChartForest W c γ δ k).clock (cavityGeneratedRawCrossAppend h r l)) : Measure _) := by
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  let H := cavityGeneratedRawCrossAppend h r l
  have hp := integral_cavityGeneratedObservedRawForest_component_replacement D μ a V c U H
    (fun σ=>G (cavityGeneratedObservedRawCrossTerminalProjection W c γ δ k σ))
  change (∫σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree,
    ∫τ : CavityGeneratedObservedRawComponentTerminal n U,
      G (cavityGeneratedObservedRawCrossTerminalProjection W c γ δ k
        (cavityGeneratedObservedRawForestReplacementTerminal V c U σ τ))
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a U H
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (V.clock H) : Measure _))=_ at hp
  rw [cavityGeneratedObservedRawCross_reindexed_clock] at hp
  refine Eq.trans ?_ hp
  apply integral_congr_ae
  refine .of_forall fun σ=>?_
  have hlaw := cavityGeneratedObservedRawCrossComponent_terminal_receiver D μ a (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
    h r l hr hl hk (fun z=>G (Function.update σ c z.1,z.2))
  refine hlaw.symm.trans ?_
  apply integral_congr_ae
  exact .of_forall fun τ=>(congrArg G
    (cavityGeneratedObservedRawCrossTerminalProjection_replacement W c γ δ k σ τ)).symm

theorem cavityGeneratedObservedRawCrossTest_eq_source
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
    (hl : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l)
    (hk : cavityGeneratedRawCrossChartHolds (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
      (cavityGeneratedRawCrossSite (W.tree c) δ) k r l)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    cavityGeneratedObservedRawCrossTest W c γ δ k F (cavityGeneratedRawCrossAppend h r l) σ=
      F (h,(cavityGeneratedObservedRawCrossTerminalProjection W c γ δ k σ).1)*
        cavitySpinOverlapDefect n
          (nativeStreamingOriginCommonClock (W.clock h c) (W.tree c)
            (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
            (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l))
          (cavityGeneratedObservedRawCrossTerminalProjection W c γ δ k σ).2.1
          (cavityGeneratedObservedRawCrossTerminalProjection W c γ δ k σ).2.2 := by
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  let τ := (cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm (σ c)
  have hd := cavityGeneratedObservedRawCross_fresh_pair_defect (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k h r l hr hl hk τ
  unfold cavityGeneratedObservedRawCrossTest
  rw [cavityGeneratedRawCrossPrefix_append]
  apply congrArg (fun x=>F (h,cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ)*x)
  exact hd.symm

end QuantitativeFollowup
