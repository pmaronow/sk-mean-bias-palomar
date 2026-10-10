module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTests
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverDefect
public import QuantitativeFollowup.SupportingGeneratedCrossOriginOldPairSpins

@[expose] public section

/-! Actual pair tags survive a computed cross-source replacement. Both
selected origins still refer to the original component. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n d : ℕ}

def crossPairLeafCast {M : ℕ}
    (U V : CavityGeneratedConstructedComponent M) (he : U=V)
    (i : ObservationLeaf U.tree) : ObservationLeaf V.tree :=
  cast (congrArg (fun A : CavityGeneratedConstructedComponent M=>ObservationLeaf A.tree) he) i

private def crossComponentPairDefect {M : ℕ}
    (U : CavityGeneratedConstructedComponent M)
    (H : CavityGeneratedHistory Paper.Overlap M) (i j : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n U) : ℝ :=
  cavitySpinOverlapDefect n
    (nativeStreamingGeneratedComponentClock U H (observationCommonLevel U.tree i j))
    (observationTerminalSpin U.tree i σ) (observationTerminalSpin U.tree j σ)

private theorem crossPairCast_defect {M : ℕ}
    (U V : CavityGeneratedConstructedComponent M) (he : U=V)
    (H : CavityGeneratedHistory Paper.Overlap M) (i j : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n V) :
    crossComponentPairDefect U H i j
      ((cavityGeneratedComponentTerminalCastEquiv (n:=n) U V he).symm σ) =
      crossComponentPairDefect V H (crossPairLeafCast U V he i)
        (crossPairLeafCast U V he j) σ := by
  cases he
  rfl

def cavityGeneratedCrossOriginPairMap
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (t : CavityGeneratedForestPair W) :
    CavityGeneratedForestPair (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k) := by
  classical
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k
  rcases t with ⟨s,i,j⟩
  by_cases hs : s=c
  · subst s
    exact ⟨c,
      crossPairLeafCast U _ (cavityGeneratedForestReplaceComponent_same V c U).symm
        (printedGeneratedOriginCrossChartOldLeaf (W.component c) γ₁ γ₂ k i),
      crossPairLeafCast U _ (cavityGeneratedForestReplaceComponent_same V c U).symm
        (printedGeneratedOriginCrossChartOldLeaf (W.component c) γ₁ γ₂ k j)⟩
  · exact ⟨s,
      crossPairLeafCast (V.component s) _ (cavityGeneratedForestReplaceComponent_other V c U s hs).symm i,
      crossPairLeafCast (V.component s) _ (cavityGeneratedForestReplaceComponent_other V c U s hs).symm j⟩

def cavityGeneratedCrossOriginFreshPair
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart) :
    CavityGeneratedForestPair (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k) :=
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k
  ⟨c,
    crossPairLeafCast U _ (cavityGeneratedForestReplaceComponent_same V c U).symm
      (printedGeneratedOriginCrossChartFirstLeaf (W.component c) γ₁ γ₂ k),
    crossPairLeafCast U _ (cavityGeneratedForestReplaceComponent_same V c U).symm
      (printedGeneratedOriginCrossChartSecondLeaf (W.component c) γ₁ γ₂ k)⟩

theorem cavityGeneratedCrossOriginPairMap_defect
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ₁ h r)
    (hl : printedGeneratedOriginChartCell (W.component c) γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds (W.component c) γ₁ γ₂ k r l)
    (t : CavityGeneratedForestPair W)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) :
    cavityGeneratedForestPairDefect n W t h
      (cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ) =
    cavityGeneratedForestPairDefect n (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k)
      (cavityGeneratedCrossOriginPairMap W c γ₁ γ₂ k t)
      (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l) σ := by
  classical
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k
  let N := cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k
  let H := printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l
  rcases t with ⟨s,i,j⟩
  by_cases hs : s=c
  · subst s
    let τ := (cavityGeneratedForestReplacementSelectedEquiv (n:=n) V c U).symm (σ c)
    have ho : cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ c =
        (printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k τ).1 := by
      simp [cavityGeneratedCrossOriginOldTerminal,cavityGeneratedCrossOriginSelectedProjection,τ,V,U]
    have hp := printedGeneratedOriginCrossChart_old_pair_terminal_defect (W.component c) γ₁ γ₂ k
      h r l ((cavityGeneratedForest_orderSet_iff_components W h).mp hh c) hr hl hk i j τ
    have he := crossPairCast_defect U (N.component c)
      (cavityGeneratedForestReplaceComponent_same V c U).symm H
      (printedGeneratedOriginCrossChartOldLeaf (W.component c) γ₁ γ₂ k i)
      (printedGeneratedOriginCrossChartOldLeaf (W.component c) γ₁ γ₂ k j) (σ c)
    have hc : W.clockTemplate.clock h c = nativeStreamingGeneratedComponentClock (W.component c) h :=
      printedGeneratedComponentClock_eq_native (W.component c) h
    have hn : N.clockTemplate.clock H c = nativeStreamingGeneratedComponentClock (N.component c) H :=
      printedGeneratedComponentClock_eq_native (N.component c) H
    change cavitySpinOverlapDefect n (W.clockTemplate.clock h c (observationCommonLevel (W.tree c) i j))
      (observationTerminalSpin (W.tree c) i (cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ c))
      (observationTerminalSpin (W.tree c) j (cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ c)) = _
    rw [ho,hc]
    have hm : cavityGeneratedCrossOriginPairMap W c γ₁ γ₂ k ⟨c,i,j⟩ =
        (⟨c,
          crossPairLeafCast U (N.component c) (cavityGeneratedForestReplaceComponent_same V c U).symm
            (printedGeneratedOriginCrossChartOldLeaf (W.component c) γ₁ γ₂ k i),
          crossPairLeafCast U (N.component c) (cavityGeneratedForestReplaceComponent_same V c U).symm
            (printedGeneratedOriginCrossChartOldLeaf (W.component c) γ₁ γ₂ k j)⟩ : CavityGeneratedForestPair N) := by
      simp only [cavityGeneratedCrossOriginPairMap,dif_pos rfl]
      rfl
    rw [hm]
    change _ = cavitySpinOverlapDefect n (N.clockTemplate.clock H c _ ) _ _
    rw [hn]
    exact hp.trans he
  · have ho : cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ s =
        (cavityGeneratedForestReplacementOtherEquiv (n:=n) V c U s hs).symm (σ s) := by
      simp only [cavityGeneratedCrossOriginOldTerminal,dif_neg hs]
      rfl
    have hc : nativeStreamingGeneratedComponentClock (V.component s) H = W.clockTemplate.clock h s := by
      rw [←printedGeneratedComponentClock_eq_native]
      exact W.reindex_clock (fun i=>i.castSucc.castSucc) h H
        (fun i=>by simp only [H,printedGeneratedOriginCrossChartAppend,Fin.snoc_castSucc]) s
    have hn : N.clockTemplate.clock H s = nativeStreamingGeneratedComponentClock (N.component s) H :=
      printedGeneratedComponentClock_eq_native (N.component s) H
    have he := crossPairCast_defect (V.component s) (N.component s)
      (cavityGeneratedForestReplaceComponent_other V c U s hs).symm H i j (σ s)
    change cavitySpinOverlapDefect n (W.clockTemplate.clock h s (observationCommonLevel (W.tree s) i j))
      (observationTerminalSpin (W.tree s) i (cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ s))
      (observationTerminalSpin (W.tree s) j (cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ s)) = _
    rw [ho,←hc]
    have hm : cavityGeneratedCrossOriginPairMap W c γ₁ γ₂ k ⟨s,i,j⟩ =
        (⟨s,
          crossPairLeafCast (V.component s) (N.component s)
            (cavityGeneratedForestReplaceComponent_other V c U s hs).symm i,
          crossPairLeafCast (V.component s) (N.component s)
            (cavityGeneratedForestReplaceComponent_other V c U s hs).symm j⟩ : CavityGeneratedForestPair N) := by
      simp only [cavityGeneratedCrossOriginPairMap,dif_neg hs]
      rfl
    rw [hm]
    change _ = cavitySpinOverlapDefect n (N.clockTemplate.clock H s _) _ _
    rw [hn]
    exact he

theorem cavityGeneratedCrossOriginFreshPair_defect
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) :
    cavityGeneratedCrossOriginFreshDefect W c γ₁ γ₂ k H σ =
    cavityGeneratedForestPairDefect n (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k)
      (cavityGeneratedCrossOriginFreshPair W c γ₁ γ₂ k) H σ := by
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k
  let N := cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k
  have he := crossPairCast_defect U (N.component c)
    (cavityGeneratedForestReplaceComponent_same V c U).symm H
    (printedGeneratedOriginCrossChartFirstLeaf (W.component c) γ₁ γ₂ k)
    (printedGeneratedOriginCrossChartSecondLeaf (W.component c) γ₁ γ₂ k) (σ c)
  have hn : N.clockTemplate.clock H c = nativeStreamingGeneratedComponentClock (N.component c) H :=
    printedGeneratedComponentClock_eq_native (N.component c) H
  change _ = cavitySpinOverlapDefect n (N.clockTemplate.clock H c _) _ _
  rw [hn]
  exact he

def cavityGeneratedCrossOriginTaggedTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedTaggedTest n W d) :
    CavityGeneratedTaggedTest n (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k) (d+1) where
  base := fun z=>A.base (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix z.1),
    cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k z.2)
  pairs := Fin.snoc (fun i=>cavityGeneratedCrossOriginPairMap W c γ₁ γ₂ k (A.pairs i))
    (cavityGeneratedCrossOriginFreshPair W c γ₁ γ₂ k)

theorem cavityGeneratedCrossOriginTaggedTest_receiver
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ₁ h r)
    (hl : printedGeneratedOriginChartCell (W.component c) γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds (W.component c) γ₁ γ₂ k r l)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) :
    cavityGeneratedCrossOriginTest W c γ₁ γ₂ k (cavityGeneratedTaggedTestValue W A)
      (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l) σ =
    cavityGeneratedTaggedTestValue (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k)
      (cavityGeneratedCrossOriginTaggedTest W c γ₁ γ₂ k A)
      (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l,σ) := by
  rw [cavityGeneratedCrossOriginTest_eq_fresh W c γ₁ γ₂ k _ h r l hh hr hl hk σ]
  unfold cavityGeneratedCrossOriginFreshTest cavityGeneratedTaggedTestValue cavityGeneratedCrossOriginTaggedTest
  simp only [Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  simp only [printedGeneratedOriginCrossChartAppend,cavityGeneratedHistoryPrefix_snoc]
  rw [cavityGeneratedCrossOriginFreshPair_defect]
  have hp : (∏i : Fin d,cavityGeneratedForestPairDefect n W (A.pairs i) h
      (cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ)) =
      ∏i : Fin d,cavityGeneratedForestPairDefect n (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k)
        (cavityGeneratedCrossOriginPairMap W c γ₁ γ₂ k (A.pairs i))
        (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l) σ := by
    apply Finset.prod_congr rfl
    intro i _
    exact cavityGeneratedCrossOriginPairMap_defect W c γ₁ γ₂ k h r l hh hr hl hk _ σ
  rw [hp,mul_assoc]
  rfl

end QuantitativeFollowup
