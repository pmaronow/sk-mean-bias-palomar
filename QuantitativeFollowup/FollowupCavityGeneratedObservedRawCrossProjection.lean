module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossGeometry
public import QuantitativeFollowup.SupportingGeneratedObservedRawForestReplacement

@[expose] public section

/-! Global terminal maps keep every old component and the ordered fresh
pair. They are actual finite-sample maps, including off-support histories,
so a successor base has the original measurable envelope everywhere. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def cavityGeneratedObservedRawCrossSelectedProjection
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    TerminalSpins (Configuration (n+1)) (W.tree c) × (Configuration (n+1)×Configuration (n+1)) :=
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  cavityGeneratedRawCrossTerminalProjection (W.tree c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
    ((cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm (σ c))

def cavityGeneratedObservedRawCrossOldTerminal
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree := by
  classical
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  exact fun i=>if hi : i=c then by
    subst i
    exact (cavityGeneratedObservedRawCrossSelectedProjection W c γ δ k σ).1
  else (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U i hi).symm (σ i)

theorem measurable_cavityGeneratedObservedRawCrossOldTerminal
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart) :
    Measurable (cavityGeneratedObservedRawCrossOldTerminal (n:=n) W c γ δ k) :=
  measurable_of_finite _

theorem measurable_cavityGeneratedObservedRawCrossBaseMap
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+2) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree=>
      (cavityGeneratedRawCrossPrefix z.1,cavityGeneratedObservedRawCrossOldTerminal W c γ δ k z.2)) := by
  have hp : Measurable (cavityGeneratedRawCrossPrefix (m:=m)) :=
    measurable_pi_iff.mpr fun i=>measurable_pi_apply i.castSucc.castSucc
  exact (hp.comp measurable_fst).prodMk
    ((measurable_cavityGeneratedObservedRawCrossOldTerminal W c γ δ k).comp measurable_snd)

def cavityGeneratedObservedRawCrossFreshDefect
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) : ℝ :=
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  let τ := (cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm (σ c)
  let i := cavityGeneratedRawCrossFirstLeaf (W.tree c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  let j := cavityGeneratedRawCrossSecondLeaf (W.tree c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  cavitySpinOverlapDefect n (U.clock H (observationCommonLevel U.tree i j))
    (observationTerminalSpin U.tree i τ) (observationTerminalSpin U.tree j τ)

def cavityGeneratedObservedRawCrossTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) : ℝ :=
  F (cavityGeneratedRawCrossPrefix H,cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ)*
    cavityGeneratedObservedRawCrossFreshDefect W c γ δ k H σ

end QuantitativeFollowup
