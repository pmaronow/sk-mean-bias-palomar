module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginPairTransport

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

def cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (i : ObservationLeaf (W.tree c)) (A : CavityGeneratedObservedRawTaggedTest n W d) :
    CavityGeneratedObservedRawTaggedTest n (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single) (d+1) where
  base := fun z => A.base
    (cavityGeneratedHistoryPrefix z.1,cavityGeneratedObservedRawSingleOriginOldTerminal W c γ .single z.2)
  pairs := Fin.snoc (fun j=>cavityGeneratedObservedRawSingleOriginPairMap W c γ .single (A.pairs j))
    (cavityGeneratedObservedRawSingleOriginOriginalFreshPair W c γ i)

def cavityGeneratedObservedRawSingleOriginCurrentTaggedTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (A : CavityGeneratedObservedRawTaggedTest n W d) :
    CavityGeneratedObservedRawTaggedTest n (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current) (d+1) where
  base := fun z => A.base
    (cavityGeneratedHistoryPrefix z.1,cavityGeneratedObservedRawSingleOriginOldTerminal W c γ .current z.2)
  pairs := Fin.snoc (fun j=>cavityGeneratedObservedRawSingleOriginPairMap W c γ .current (A.pairs j))
    (cavityGeneratedObservedRawSingleOriginCurrentPair W c γ)

theorem cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest_base_measurable
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (i : ObservationLeaf (W.tree c)) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (hA : Measurable A.base) :
    Measurable (cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A).base :=
  hA.comp (measurable_cavityGeneratedObservedRawSingleOriginBaseProjection W c γ .single)

theorem cavityGeneratedObservedRawSingleOriginCurrentTaggedTest_base_measurable
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    Measurable (cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A).base :=
  hA.comp (measurable_cavityGeneratedObservedRawSingleOriginBaseProjection W c γ .current)

theorem cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest_base_bound
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (i : ObservationLeaf (W.tree c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (C : ℝ) (hA : ∀z,|A.base z|≤C) :
    ∀z,|(cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A).base z|≤C :=
  fun z=>hA _

theorem cavityGeneratedObservedRawSingleOriginCurrentTaggedTest_base_bound
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (C : ℝ) (hA : ∀z,|A.base z|≤C) :
    ∀z,|(cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A).base z|≤C :=
  fun z=>hA _

theorem cavityGeneratedObservedRawSingleOriginOriginalFreshTest_pair
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c)) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).tree) :
    cavityGeneratedObservedRawSingleOriginOriginalFreshTest W c γ F i
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ =
    F (h,cavityGeneratedObservedRawSingleOriginOldTerminal W c γ .single σ) *
      cavityGeneratedObservedRawPairDefect (n:=n) (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
        (cavityGeneratedObservedRawSingleOriginOriginalFreshPair W c γ i)
        (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ := by
  classical
  let U := cavityGeneratedObservedRawChartComponent (W.component c) γ .single
  let V := cavityGeneratedObservedRawSingleOriginChartForest W c γ .single
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)
  let η := (cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) (W.reindex Fin.castSucc) c U).symm (σ c)
  have hp := cavityGeneratedObservedRawChartOriginalFreshTest_terminal (n:=n) (W.component c) γ h r hr (fun _=>1) i η
  simp only [nativeStreamingOriginalFreshSpinTest,one_mul] at hp
  have hc := cavityGeneratedObservedRawComponentLeafForward_pair_defect (n:=n) U (V.component c)
    (cavityGeneratedObservedRawForestReplaceComponent_same (W.reindex Fin.castSucc) c U).symm H
    (cavityGeneratedObservedRawChartOldLeaf (W.component c) γ .single i)
    (cavityGeneratedObservedRawChartFreshLeaf (W.component c) γ) (σ c)
  change cavitySpinOverlapDefect n
    (nativeStreamingOriginCommonClock (CavityGeneratedObservedRawComponent.clock (W.component c) h)
      (W.tree c) (.vertex (observationLeafVertex (W.tree c) i))
      (cavityGeneratedObservedRawChartOrigin (W.component c) γ r))
    (observationTerminalSpin (W.tree c) i _) _ = _ at hp
  change _ = cavitySpinOverlapDefect n
    (CavityGeneratedObservedRawComponent.clock (V.component c) H
      (observationCommonLevel (V.tree c) _ _))
    (observationTerminalSpin (V.tree c) _ (σ c))
    (observationTerminalSpin (V.tree c) _ (σ c)) at hc
  unfold cavityGeneratedObservedRawSingleOriginOriginalFreshTest
  simp only [cavityGeneratedObservedRawSingleOriginTerminalProjection,
    cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last,
    cavityGeneratedObservedRawChartOrigin_clock]
  apply congrArg (fun x=>F (h,cavityGeneratedObservedRawSingleOriginOldTerminal W c γ .single σ)*x)
  unfold cavityGeneratedObservedRawPairDefect
  rw [cavityGeneratedObservedRawSingleOriginOldTerminal_selected]
  simpa [cavityGeneratedObservedRawSingleOriginOriginalFreshPair,cavityGeneratedObservedRawSingleOriginOldLeaf,
    cavityGeneratedObservedRawSingleOriginTerminalProjection,cavityGeneratedObservedRawSingleOriginSelectedProjection,
    cavityGeneratedObservedRawForestReplacementSelectedEquiv,U,V,H,η,
    CavityGeneratedObservedRawForest.tree,CavityGeneratedObservedRawForest.clock,
    CavityGeneratedObservedRawForest.depth] using hp.trans hc

theorem cavityGeneratedObservedRawSingleOriginCurrentTest_pair
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).tree) :
    cavityGeneratedObservedRawSingleOriginCurrentTest W c γ F
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ =
    F (h,cavityGeneratedObservedRawSingleOriginOldTerminal W c γ .current σ) *
      cavityGeneratedObservedRawPairDefect (n:=n) (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
        (cavityGeneratedObservedRawSingleOriginCurrentPair W c γ)
        (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ := by
  classical
  let U := cavityGeneratedObservedRawChartComponent (W.component c) γ .current
  let V := cavityGeneratedObservedRawSingleOriginChartForest W c γ .current
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)
  let η := (cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) (W.reindex Fin.castSucc) c U).symm (σ c)
  have hp := cavityGeneratedObservedRawChartCurrentTest_terminal (n:=n) (W.component c) γ h r hr (fun _=>1) η
  simp only [nativeStreamingDefectSpinTest,one_mul] at hp
  have hc := cavityGeneratedObservedRawComponentLeafForward_pair_defect (n:=n) U (V.component c)
    (cavityGeneratedObservedRawForestReplaceComponent_same (W.reindex Fin.castSucc) c U).symm H
    (cavityGeneratedObservedRawChartCurrentLeaf (W.component c) γ false)
    (cavityGeneratedObservedRawChartCurrentLeaf (W.component c) γ true) (σ c)
  change _ = cavitySpinOverlapDefect n
    (CavityGeneratedObservedRawComponent.clock (V.component c) H
      (observationCommonLevel (V.tree c) _ _))
    (observationTerminalSpin (V.tree c) _ (σ c))
    (observationTerminalSpin (V.tree c) _ (σ c)) at hc
  unfold cavityGeneratedObservedRawSingleOriginCurrentTest
  simp only [cavityGeneratedObservedRawSingleOriginTerminalProjection,
    cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last,
    cavityGeneratedObservedRawChartOrigin_clock]
  apply congrArg (fun x=>F (h,cavityGeneratedObservedRawSingleOriginOldTerminal W c γ .current σ)*x)
  unfold cavityGeneratedObservedRawPairDefect
  simpa [cavityGeneratedObservedRawSingleOriginCurrentPair,cavityGeneratedObservedRawSingleOriginTerminalProjection,
    cavityGeneratedObservedRawSingleOriginSelectedProjection,cavityGeneratedObservedRawForestReplacementSelectedEquiv,
    U,V,H,η,CavityGeneratedObservedRawForest.tree,CavityGeneratedObservedRawForest.clock,
    CavityGeneratedObservedRawForest.depth] using hp.trans hc

theorem cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest_value
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (i : ObservationLeaf (W.tree c))
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).tree) :
    cavityGeneratedObservedRawSingleOriginOriginalFreshTest W c γ (cavityGeneratedObservedRawTaggedValue W A) i
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ =
    cavityGeneratedObservedRawTaggedValue (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
      (cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A)
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r),σ) := by
  rw [cavityGeneratedObservedRawSingleOriginOriginalFreshTest_pair W c γ _ i h r hr]
  unfold cavityGeneratedObservedRawTaggedValue cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest
  rw [Fin.prod_univ_castSucc]
  simp only [cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last]
  have hp : (∏j : Fin d, cavityGeneratedObservedRawPairDefect (n:=n) W (A.pairs j) h
      (cavityGeneratedObservedRawSingleOriginOldTerminal W c γ .single σ)) =
      ∏j : Fin d,cavityGeneratedObservedRawPairDefect (n:=n)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
        (cavityGeneratedObservedRawSingleOriginPairMap W c γ .single (A.pairs j))
        (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ := by
    apply Finset.prod_congr rfl
    intro j hj
    exact cavityGeneratedObservedRawSingleOriginPairMap_defect W c γ .single (A.pairs j) h r hr σ
  rw [hp,mul_assoc]

theorem cavityGeneratedObservedRawSingleOriginCurrentTaggedTest_value
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).tree) :
    cavityGeneratedObservedRawSingleOriginCurrentTest W c γ (cavityGeneratedObservedRawTaggedValue W A)
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ =
    cavityGeneratedObservedRawTaggedValue (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
      (cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A)
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r),σ) := by
  rw [cavityGeneratedObservedRawSingleOriginCurrentTest_pair W c γ _ h r hr]
  unfold cavityGeneratedObservedRawTaggedValue cavityGeneratedObservedRawSingleOriginCurrentTaggedTest
  rw [Fin.prod_univ_castSucc]
  simp only [cavityGeneratedHistoryPrefix_snoc,Fin.snoc_castSucc,Fin.snoc_last]
  have hp : (∏j : Fin d, cavityGeneratedObservedRawPairDefect (n:=n) W (A.pairs j) h
      (cavityGeneratedObservedRawSingleOriginOldTerminal W c γ .current σ)) =
      ∏j : Fin d,cavityGeneratedObservedRawPairDefect (n:=n)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
        (cavityGeneratedObservedRawSingleOriginPairMap W c γ .current (A.pairs j))
        (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ := by
    apply Finset.prod_congr rfl
    intro j hj
    exact cavityGeneratedObservedRawSingleOriginPairMap_defect W c γ .current (A.pairs j) h r hr σ
  rw [hp,mul_assoc]

theorem cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest_event
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (i : ObservationLeaf (W.tree c)) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z∈cavityGeneratedObservedRawSingleOriginChartEvent W c γ)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).tree) :
    cavityGeneratedObservedRawSingleOriginOriginalFreshTest W c γ (cavityGeneratedObservedRawTaggedValue W A) i
      (Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)) σ =
    cavityGeneratedObservedRawTaggedValue (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
      (cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A)
      (Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z),σ) := by
  have he := cavityGeneratedObservedRawOriginSelectionClock_eq_chart (W.component c) z
  rw [hz.1] at he
  change cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z = _ at he
  rw [he]
  exact cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest_value
    W c γ A i z.1 (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) hz.2.2 σ

theorem cavityGeneratedObservedRawSingleOriginCurrentTaggedTest_event
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z∈cavityGeneratedObservedRawSingleOriginChartEvent W c γ)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).tree) :
    cavityGeneratedObservedRawSingleOriginCurrentTest W c γ (cavityGeneratedObservedRawTaggedValue W A)
      (Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)) σ =
    cavityGeneratedObservedRawTaggedValue (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
      (cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A)
      (Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z),σ) := by
  have he := cavityGeneratedObservedRawOriginSelectionClock_eq_chart (W.component c) z
  rw [hz.1] at he
  change cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z = _ at he
  rw [he]
  exact cavityGeneratedObservedRawSingleOriginCurrentTaggedTest_value
    W c γ A z.1 (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) hz.2.2 σ

end QuantitativeFollowup
