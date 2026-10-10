module
public import QuantitativeFollowup.SupportingGeneratedSingleOriginPairTransport

@[expose] public section

/-! The exact one-origin source callbacks are successor tagged tests.
The new pair is appended to the transported old tags; their joint base
observable retains the original history and every old terminal spin. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}

def cavityGeneratedSingleOriginOriginalFreshTaggedTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (i : ObservationLeaf (W.tree c)) (A : CavityGeneratedTaggedTest n W d) :
    CavityGeneratedTaggedTest n (cavityGeneratedSingleOriginChartForest W c γ .single) (d+1) where
  base := fun z => A.base
    (cavityGeneratedHistoryPrefix z.1,cavityGeneratedSingleOriginOldTerminal W c γ .single z.2)
  pairs := Fin.snoc (fun j=>cavityGeneratedSingleOriginPairMap W c γ .single (A.pairs j))
    (cavityGeneratedSingleOriginOriginalFreshPair W c γ i)

def cavityGeneratedSingleOriginCurrentTaggedTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (A : CavityGeneratedTaggedTest n W d) :
    CavityGeneratedTaggedTest n (cavityGeneratedSingleOriginChartForest W c γ .current) (d+1) where
  base := fun z => A.base
    (cavityGeneratedHistoryPrefix z.1,cavityGeneratedSingleOriginOldTerminal W c γ .current z.2)
  pairs := Fin.snoc (fun j=>cavityGeneratedSingleOriginPairMap W c γ .current (A.pairs j))
    (cavityGeneratedSingleOriginCurrentPair W c γ)

theorem cavityGeneratedSingleOriginOriginalFreshTest_pair
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c)) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedSingleOriginChartForest W c γ .single).tree) :
    cavityGeneratedSingleOriginOriginalFreshTest W c γ F i
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ =
    F (h,cavityGeneratedSingleOriginOldTerminal W c γ .single σ) *
      cavityGeneratedForestPairDefect n (cavityGeneratedSingleOriginChartForest W c γ .single)
        (cavityGeneratedSingleOriginOriginalFreshPair W c γ i)
        (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ := by
  classical
  let U := printedGeneratedOriginChartComponent (W.component c) γ .single
  let V := cavityGeneratedSingleOriginChartForest W c γ .single
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)
  let η := (cavityGeneratedForestReplacementSelectedEquiv (n:=n) (W.reindex Fin.castSucc) c U).symm (σ c)
  have hhU := (cavityGeneratedForest_orderSet_iff_components W h).mp hh c
  have hp := printedGeneratedOriginChartOriginalFresh_defect (n:=n) (W.component c) γ h r hhU hr i η
  have hc := cavityGeneratedComponentLeafCastEquiv_pair_defect (n:=n) U (V.component c)
    (cavityGeneratedForestReplaceComponent_same (W.reindex Fin.castSucc) c U).symm H
    (printedGeneratedOriginChartOldLeaf (W.component c) γ .single i)
    (printedGeneratedOriginChartFreshLeaf (W.component c) γ) (σ c)
  change cavitySpinOverlapDefect n
    (nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock (W.component c) h)
      (W.tree c) (.vertex (observationLeafVertex (W.tree c) i))
      (printedGeneratedOriginChartOrigin (W.component c) γ r))
    (observationTerminalSpin (W.tree c) i _) _ = _ at hp
  change _ = cavitySpinOverlapDefect n
    (nativeStreamingGeneratedComponentClock (V.component c) H
      (observationCommonLevel (V.tree c) _ _))
    (observationTerminalSpin (V.tree c) _ (σ c))
    (observationTerminalSpin (V.tree c) _ (σ c)) at hc
  unfold cavityGeneratedSingleOriginOriginalFreshTest
  simp only [cavityGeneratedSingleOriginTerminalProjection,
    cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last,
    cavityGeneratedOriginChartOrigin_clock]
  apply congrArg (fun x=>F (h,cavityGeneratedSingleOriginOldTerminal W c γ .single σ)*x)
  unfold cavityGeneratedForestPairDefect
  rw [cavityGeneratedSingleOriginOldTerminal_selected]
  rw [←printedGeneratedComponentClock_of_forest W h c,printedGeneratedComponentClock_eq_native]
  change _ = cavitySpinOverlapDefect n (printedGeneratedComponentClock (V.component c) H _)
    (observationTerminalSpin _ _ (σ c)) (observationTerminalSpin _ _ (σ c))
  rw [printedGeneratedComponentClock_eq_native]
  simpa [cavityGeneratedSingleOriginOriginalFreshPair,cavityGeneratedSingleOriginOldLeaf,
    cavityGeneratedSingleOriginTerminalProjection,cavityGeneratedSingleOriginSelectedProjection,
    cavityGeneratedForestReplacementSelectedEquiv,U,V,H,η] using hp.trans hc

theorem cavityGeneratedSingleOriginCurrentTest_pair
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedSingleOriginChartForest W c γ .current).tree) :
    cavityGeneratedSingleOriginCurrentTest W c γ F
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ =
    F (h,cavityGeneratedSingleOriginOldTerminal W c γ .current σ) *
      cavityGeneratedForestPairDefect n (cavityGeneratedSingleOriginChartForest W c γ .current)
        (cavityGeneratedSingleOriginCurrentPair W c γ)
        (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ := by
  classical
  let U := printedGeneratedOriginChartComponent (W.component c) γ .current
  let V := cavityGeneratedSingleOriginChartForest W c γ .current
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)
  let η := (cavityGeneratedForestReplacementSelectedEquiv (n:=n) (W.reindex Fin.castSucc) c U).symm (σ c)
  have hhU := (cavityGeneratedForest_orderSet_iff_components W h).mp hh c
  have hp := printedGeneratedOriginChartCurrent_defect (n:=n) (W.component c) γ h r hhU hr η
  have hc := cavityGeneratedComponentLeafCastEquiv_pair_defect (n:=n) U (V.component c)
    (cavityGeneratedForestReplaceComponent_same (W.reindex Fin.castSucc) c U).symm H
    (printedGeneratedOriginChartCurrentLeaf (W.component c) γ false)
    (printedGeneratedOriginChartCurrentLeaf (W.component c) γ true) (σ c)
  change _ = cavitySpinOverlapDefect n
    (nativeStreamingGeneratedComponentClock (V.component c) H
      (observationCommonLevel (V.tree c) _ _))
    (observationTerminalSpin (V.tree c) _ (σ c))
    (observationTerminalSpin (V.tree c) _ (σ c)) at hc
  unfold cavityGeneratedSingleOriginCurrentTest
  simp only [cavityGeneratedSingleOriginTerminalProjection,
    cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last,
    cavityGeneratedOriginChartOrigin_clock]
  apply congrArg (fun x=>F (h,cavityGeneratedSingleOriginOldTerminal W c γ .current σ)*x)
  unfold cavityGeneratedForestPairDefect
  rw [←printedGeneratedComponentClock_of_forest W h c,printedGeneratedComponentClock_eq_native]
  change _ = cavitySpinOverlapDefect n (printedGeneratedComponentClock (V.component c) H _)
    (observationTerminalSpin _ _ (σ c)) (observationTerminalSpin _ _ (σ c))
  rw [printedGeneratedComponentClock_eq_native]
  simpa [cavityGeneratedSingleOriginCurrentPair,cavityGeneratedSingleOriginTerminalProjection,
    cavityGeneratedSingleOriginSelectedProjection,cavityGeneratedForestReplacementSelectedEquiv,
    U,V,H,η] using hp.trans hc

theorem cavityGeneratedSingleOriginOriginalFreshTaggedTest_value
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (A : CavityGeneratedTaggedTest n W d) (i : ObservationLeaf (W.tree c))
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedSingleOriginChartForest W c γ .single).tree) :
    cavityGeneratedSingleOriginOriginalFreshTest W c γ (cavityGeneratedTaggedTestValue W A) i
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ =
    cavityGeneratedTaggedTestValue (cavityGeneratedSingleOriginChartForest W c γ .single)
      (cavityGeneratedSingleOriginOriginalFreshTaggedTest W c γ i A)
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r),σ) := by
  rw [cavityGeneratedSingleOriginOriginalFreshTest_pair W c γ _ i h r hh hr]
  unfold cavityGeneratedTaggedTestValue cavityGeneratedSingleOriginOriginalFreshTaggedTest
  rw [Fin.prod_univ_castSucc]
  simp only [cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last]
  have hp : (∏j : Fin d, cavityGeneratedForestPairDefect n W (A.pairs j) h
      (cavityGeneratedSingleOriginOldTerminal W c γ .single σ)) =
      ∏j : Fin d,cavityGeneratedForestPairDefect n
        (cavityGeneratedSingleOriginChartForest W c γ .single)
        (cavityGeneratedSingleOriginPairMap W c γ .single (A.pairs j))
        (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ := by
    apply Finset.prod_congr rfl
    intro j hj
    exact cavityGeneratedSingleOriginPairMap_defect W c γ .single (A.pairs j) h r hh hr σ
  rw [hp,mul_assoc]

theorem cavityGeneratedSingleOriginCurrentTaggedTest_value
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (A : CavityGeneratedTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedSingleOriginChartForest W c γ .current).tree) :
    cavityGeneratedSingleOriginCurrentTest W c γ (cavityGeneratedTaggedTestValue W A)
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ =
    cavityGeneratedTaggedTestValue (cavityGeneratedSingleOriginChartForest W c γ .current)
      (cavityGeneratedSingleOriginCurrentTaggedTest W c γ A)
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r),σ) := by
  rw [cavityGeneratedSingleOriginCurrentTest_pair W c γ _ h r hh hr]
  unfold cavityGeneratedTaggedTestValue cavityGeneratedSingleOriginCurrentTaggedTest
  rw [Fin.prod_univ_castSucc]
  simp only [cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last]
  have hp : (∏j : Fin d, cavityGeneratedForestPairDefect n W (A.pairs j) h
      (cavityGeneratedSingleOriginOldTerminal W c γ .current σ)) =
      ∏j : Fin d,cavityGeneratedForestPairDefect n
        (cavityGeneratedSingleOriginChartForest W c γ .current)
        (cavityGeneratedSingleOriginPairMap W c γ .current (A.pairs j))
        (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ := by
    apply Finset.prod_congr rfl
    intro j hj
    exact cavityGeneratedSingleOriginPairMap_defect W c γ .current (A.pairs j) h r hh hr σ
  rw [hp,mul_assoc]

theorem cavityGeneratedSingleOriginOriginalFreshTaggedTest_event
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (i : ObservationLeaf (W.tree c)) (A : CavityGeneratedTaggedTest n W d)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z∈cavityGeneratedSingleOriginChartEvent W c γ)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedSingleOriginChartForest W c γ .single).tree) :
    cavityGeneratedSingleOriginOriginalFreshTest W c γ (cavityGeneratedTaggedTestValue W A) i
      (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z)) σ =
    cavityGeneratedTaggedTestValue (cavityGeneratedSingleOriginChartForest W c γ .single)
      (cavityGeneratedSingleOriginOriginalFreshTaggedTest W c γ i A)
      (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z),σ) := by
  have he := cavityGeneratedOriginSelectionClock_eq_chart W c z
  rw [hz.1] at he
  rw [he]
  exact cavityGeneratedSingleOriginOriginalFreshTaggedTest_value
    W c γ A i z.1 (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) hz.2.1 hz.2.2 σ

theorem cavityGeneratedSingleOriginCurrentTaggedTest_event
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (A : CavityGeneratedTaggedTest n W d)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z∈cavityGeneratedSingleOriginChartEvent W c γ)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedSingleOriginChartForest W c γ .current).tree) :
    cavityGeneratedSingleOriginCurrentTest W c γ (cavityGeneratedTaggedTestValue W A)
      (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z)) σ =
    cavityGeneratedTaggedTestValue (cavityGeneratedSingleOriginChartForest W c γ .current)
      (cavityGeneratedSingleOriginCurrentTaggedTest W c γ A)
      (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z),σ) := by
  have he := cavityGeneratedOriginSelectionClock_eq_chart W c z
  rw [hz.1] at he
  rw [he]
  exact cavityGeneratedSingleOriginCurrentTaggedTest_value
    W c γ A z.1 (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) hz.2.1 hz.2.2 σ

end QuantitativeFollowup
