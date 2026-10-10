module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverFubini
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverLeafSpins

@[expose] public section

/-! The transported cross callback uses the actual two fresh terminal leaves
and the actual common level of the computed enlarged component. -/
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

def cavityGeneratedCrossOriginFreshDefect
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) : ℝ :=
  let U := printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k
  let τ := (cavityGeneratedForestReplacementSelectedEquiv (n:=n)
    (W.reindex (fun i=>i.castSucc.castSucc)) c U).symm (σ c)
  cavitySpinOverlapDefect n
    (nativeStreamingGeneratedComponentClock U H
      (observationCommonLevel U.tree
        (printedGeneratedOriginCrossChartFirstLeaf (W.component c) γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartSecondLeaf (W.component c) γ₁ γ₂ k)))
    (observationTerminalSpin U.tree (printedGeneratedOriginCrossChartFirstLeaf (W.component c) γ₁ γ₂ k) τ)
    (observationTerminalSpin U.tree (printedGeneratedOriginCrossChartSecondLeaf (W.component c) γ₁ γ₂ k) τ)

def cavityGeneratedCrossOriginFreshTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) : ℝ :=
  F (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H),
    cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ) *
      cavityGeneratedCrossOriginFreshDefect W c γ₁ γ₂ k H σ

theorem cavityGeneratedCrossOriginTest_eq_fresh
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ₁ h r)
    (hl : printedGeneratedOriginChartCell (W.component c) γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds (W.component c) γ₁ γ₂ k r l)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) :
    cavityGeneratedCrossOriginTest W c γ₁ γ₂ k F
      (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l) σ =
    cavityGeneratedCrossOriginFreshTest W c γ₁ γ₂ k F
      (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l) σ := by
  let H := printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l
  let U := printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k
  let τ := (cavityGeneratedForestReplacementSelectedEquiv (n:=n)
    (W.reindex (fun i=>i.castSucc.castSucc)) c U).symm (σ c)
  have hclock : printedGeneratedOriginCrossChartSourceClock (W.component c) γ₁ γ₂ H =
      nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock (W.component c) h)
        (W.tree c) (printedGeneratedOriginCrossChartOrigin (W.component c) γ₁ r)
        (printedGeneratedOriginCrossChartOrigin (W.component c) γ₂ l) := by
    simp only [H,printedGeneratedOriginCrossChartSourceClock,printedGeneratedOriginCrossChartAppend,
      cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last,
      printedGeneratedOriginCrossChartOrigin_chartClock]
    rfl
  have hp := printedGeneratedOriginCrossChart_literal_terminal_defect (W.component c) γ₁ γ₂ k
    h r l ((cavityGeneratedForest_orderSet_iff_components W h).mp hh c) hr hl hk τ
  change F (_,cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ) *
      cavitySpinOverlapDefect n (printedGeneratedOriginCrossChartSourceClock (W.component c) γ₁ γ₂ H)
        (printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k τ).2.1
        (printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k τ).2.2 =
    F (_,cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ) * _
  rw [hclock]
  exact congrArg (fun x : ℝ=>F
    (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H),
      cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ) * x) hp

end QuantitativeFollowup
