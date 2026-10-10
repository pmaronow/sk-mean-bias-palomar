module
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureForestReceiver

@[expose] public section

/-! Every old raw forest pair is transported through the genuine component
replacement and terminal projection. The actual fresh pair is appended as
a new tag. Its physical clock is identified only on the honest source event. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n d : ℕ}

def rawFuturePairLeafCast {M : ℕ} (U U' : CavityGeneratedObservedRawComponent M)
    (he : U=U') (i : ObservationLeaf U.tree) : ObservationLeaf U'.tree :=
  cast (congrArg (fun V : CavityGeneratedObservedRawComponent M => ObservationLeaf V.tree) he) i

private theorem rawFuturePairLeafCast_defect {M : ℕ}
    (U U' : CavityGeneratedObservedRawComponent M) (he : U=U')
    (h : CavityGeneratedHistory Paper.Overlap M) (i k : ObservationLeaf U.tree)
    (σ : CavityGeneratedObservedRawComponentTerminal n U') :
    cavitySpinOverlapDefect n
      (U'.clock h (observationCommonLevel U'.tree
        (rawFuturePairLeafCast U U' he i) (rawFuturePairLeafCast U U' he k)))
      (observationTerminalSpin U'.tree (rawFuturePairLeafCast U U' he i) σ)
      (observationTerminalSpin U'.tree (rawFuturePairLeafCast U U' he k) σ) =
    cavitySpinOverlapDefect n (U.clock h (observationCommonLevel U.tree i k))
      (observationTerminalSpin U.tree i
        ((cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U U' he).symm σ))
      (observationTerminalSpin U.tree k
        ((cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U U' he).symm σ)) := by
  cases he
  rfl

def rawFuturePairSelectedLeaf (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c))
    (i : ObservationLeaf (cavityGeneratedObservedRawFutureComponent (W.component c) γ j).tree) :
    ObservationLeaf ((cavityGeneratedObservedRawFutureForest W c γ j).tree c) :=
  rawFuturePairLeafCast _ _
    (cavityGeneratedObservedRawForestReplaceComponent_same
      (W.reindex (fun i => i.castSucc.castSucc)) c
      (cavityGeneratedObservedRawFutureComponent (W.component c) γ j)).symm i

def rawFuturePairOldLeaf (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c)) (i : Fin W.componentCount) (b : ObservationLeaf (W.tree i)) :
    ObservationLeaf ((cavityGeneratedObservedRawFutureForest W c γ j).tree i) := by
  classical
  by_cases hi : i=c
  · subst i
    exact rawFuturePairSelectedLeaf W c γ j
      (cavityGeneratedObservedRawFutureOldLeaf (W.tree c) γ j b)
  · exact rawFuturePairLeafCast _ _
      (cavityGeneratedObservedRawForestReplaceComponent_other
        (W.reindex (fun i => i.castSucc.castSucc)) c
        (cavityGeneratedObservedRawFutureComponent (W.component c) γ j) i hi).symm b

def cavityGeneratedObservedRawFuturePairMap (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c)) (t : CavityGeneratedObservedRawPair W) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawFutureForest W c γ j) where
  component := t.component
  first := rawFuturePairOldLeaf W c γ j t.component t.first
  second := rawFuturePairOldLeaf W c γ j t.component t.second

def cavityGeneratedObservedRawFutureFreshPair (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c)) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawFutureForest W c γ j) where
  component := c
  first := rawFuturePairSelectedLeaf W c γ j
    (cavityGeneratedObservedRawFutureFirstLeaf (W.tree c) γ j)
  second := rawFuturePairSelectedLeaf W c γ j
    (cavityGeneratedObservedRawFutureSecondLeaf (W.tree c) γ j)

private theorem rawFutureComponent_oldPair_defect
    (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (hH : H ∈ cavityGeneratedObservedRawFutureComponentEvent U γ j)
    (i k : ObservationLeaf U.tree)
    (σ : CavityGeneratedObservedRawComponentTerminal n (cavityGeneratedObservedRawFutureComponent U γ j)) :
    cavitySpinOverlapDefect n
      (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) (observationCommonLevel U.tree i k))
      (observationTerminalSpin U.tree i (cavityGeneratedObservedRawFutureTerminalProject U.tree γ j σ).1)
      (observationTerminalSpin U.tree k (cavityGeneratedObservedRawFutureTerminalProject U.tree γ j σ).1) =
    cavitySpinOverlapDefect n
      ((cavityGeneratedObservedRawFutureComponent U γ j).clock H
        (observationCommonLevel _ (cavityGeneratedObservedRawFutureOldLeaf U.tree γ j i)
          (cavityGeneratedObservedRawFutureOldLeaf U.tree γ j k)))
      (observationTerminalSpin _ (cavityGeneratedObservedRawFutureOldLeaf U.tree γ j i) σ)
      (observationTerminalSpin _ (cavityGeneratedObservedRawFutureOldLeaf U.tree γ j k) σ) := by
  rw [cavityGeneratedObservedRawFutureComponent_clock_on_event U γ j H hH]
  change _ = cavitySpinOverlapDefect n
    (cavityGeneratedObservedRawFutureClock (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)) U.tree γ j
      (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark) _) _ _
  rw [cavityGeneratedObservedRawFutureOldLeaves_commonClock,
    cavityGeneratedObservedRawFutureTerminalProject_old_leaf,
    cavityGeneratedObservedRawFutureTerminalProject_old_leaf]

theorem cavityGeneratedObservedRawFuturePairMap_defect
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (t : CavityGeneratedObservedRawPair W)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedObservedRawFutureSourceEvent W c γ j)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawFutureForest W c γ j).depth
      (cavityGeneratedObservedRawFutureForest W c γ j).tree) :
    cavityGeneratedObservedRawPairDefect W t z.1.1 (cavityGeneratedObservedRawFutureOldTerminal W c γ j σ) =
      cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawFutureForest W c γ j)
        (cavityGeneratedObservedRawFuturePairMap W c γ j t) (cavityGeneratedObservedRawFutureAppend W c z) σ := by
  classical
  rcases t with ⟨i,b,e⟩
  let V := W.reindex (fun i => i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawFutureComponent (W.component c) γ j
  let W' := cavityGeneratedObservedRawFutureForest W c γ j
  let H := cavityGeneratedObservedRawFutureAppend W c z
  have hprefix := cavityGeneratedObservedRawFutureAppend_prefix W c z
  by_cases hi : i=c
  · subst i
    let τ := (cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm (σ c)
    have ho : cavityGeneratedObservedRawFutureOldTerminal W c γ j σ c =
        (cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j τ).1 := by
      simp only [cavityGeneratedObservedRawFutureOldTerminal,dif_pos rfl,cast_eq]
      rfl
    have hp := rawFutureComponent_oldPair_defect (W.component c) γ j H hz.2.2 b e τ
    rw [hprefix] at hp
    have he := rawFuturePairLeafCast_defect U (W'.component c)
      (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm H
      (cavityGeneratedObservedRawFutureOldLeaf (W.tree c) γ j b)
      (cavityGeneratedObservedRawFutureOldLeaf (W.tree c) γ j e) (σ c)
    change cavitySpinOverlapDefect n (W.clock z.1.1 c (observationCommonLevel (W.tree c) b e))
      (observationTerminalSpin (W.tree c) b (cavityGeneratedObservedRawFutureOldTerminal W c γ j σ c))
      (observationTerminalSpin (W.tree c) e (cavityGeneratedObservedRawFutureOldTerminal W c γ j σ c)) = _
    rw [ho]
    have hm : cavityGeneratedObservedRawFuturePairMap W c γ j ⟨c,b,e⟩ =
        (⟨c,
          rawFuturePairLeafCast U (W'.component c) (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm
            (cavityGeneratedObservedRawFutureOldLeaf (W.tree c) γ j b),
          rawFuturePairLeafCast U (W'.component c) (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm
            (cavityGeneratedObservedRawFutureOldLeaf (W.tree c) γ j e)⟩ : CavityGeneratedObservedRawPair W') := by
      simp only [cavityGeneratedObservedRawFuturePairMap,rawFuturePairOldLeaf,dif_pos rfl,dite_true]
      rfl
    rw [hm]
    exact hp.trans he.symm
  · have ho : cavityGeneratedObservedRawFutureOldTerminal W c γ j σ i =
        (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U i hi).symm (σ i) := by
      simp only [cavityGeneratedObservedRawFutureOldTerminal,dif_neg hi]
      rfl
    have hc : (V.component i).clock H = W.clock z.1.1 i := by
      change W.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) i = _
      rw [hprefix]
    have he := rawFuturePairLeafCast_defect (V.component i) (W'.component i)
      (cavityGeneratedObservedRawForestReplaceComponent_other V c U i hi).symm H b e (σ i)
    change cavitySpinOverlapDefect n (W.clock z.1.1 i (observationCommonLevel (W.tree i) b e))
      (observationTerminalSpin (W.tree i) b (cavityGeneratedObservedRawFutureOldTerminal W c γ j σ i))
      (observationTerminalSpin (W.tree i) e (cavityGeneratedObservedRawFutureOldTerminal W c γ j σ i)) = _
    rw [ho,←hc]
    have hm : cavityGeneratedObservedRawFuturePairMap W c γ j ⟨i,b,e⟩ =
        (⟨i,
          rawFuturePairLeafCast (V.component i) (W'.component i)
            (cavityGeneratedObservedRawForestReplaceComponent_other V c U i hi).symm b,
          rawFuturePairLeafCast (V.component i) (W'.component i)
            (cavityGeneratedObservedRawForestReplaceComponent_other V c U i hi).symm e⟩ : CavityGeneratedObservedRawPair W') := by
      simp only [cavityGeneratedObservedRawFuturePairMap,rawFuturePairOldLeaf,dif_neg hi]
      rfl
    rw [hm]
    exact he.symm

theorem cavityGeneratedObservedRawFutureFreshPair_defect
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedObservedRawFutureSourceEvent W c γ j)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawFutureForest W c γ j).depth
      (cavityGeneratedObservedRawFutureForest W c γ j).tree) :
    cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawFutureForest W c γ j)
      (cavityGeneratedObservedRawFutureFreshPair W c γ j) (cavityGeneratedObservedRawFutureAppend W c z) σ =
      cavitySpinOverlapDefect n z.2 (cavityGeneratedObservedRawFutureChosenTerminal W c γ j σ).2.1
        (cavityGeneratedObservedRawFutureChosenTerminal W c γ j σ).2.2 := by
  let V := W.reindex (fun i => i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawFutureComponent (W.component c) γ j
  let H := cavityGeneratedObservedRawFutureAppend W c z
  let τ := (cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm (σ c)
  let τp : TerminalSpins (Configuration (n+1))
      (cavityGeneratedObservedRawFutureTree (W.tree c) γ j) := τ
  have he := rawFuturePairLeafCast_defect U
    ((cavityGeneratedObservedRawFutureForest W c γ j).component c)
    (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm H
    (cavityGeneratedObservedRawFutureFirstLeaf (W.tree c) γ j)
    (cavityGeneratedObservedRawFutureSecondLeaf (W.tree c) γ j) (σ c)
  refine he.trans ?_
  rw [cavityGeneratedObservedRawFutureComponent_clock_on_event (W.component c) γ j H hz.2.2]
  change cavitySpinOverlapDefect n
    (cavityGeneratedObservedRawFutureClock ((W.component c).clock
      (cavityGeneratedObservedRawFutureHistoryPrefix H)) (W.tree c) γ j
      (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark)
      (observationCommonLevel (cavityGeneratedObservedRawFutureTree (W.tree c) γ j)
        (cavityGeneratedObservedRawFutureFirstLeaf (W.tree c) γ j)
        (cavityGeneratedObservedRawFutureSecondLeaf (W.tree c) γ j)))
    (observationTerminalSpin (cavityGeneratedObservedRawFutureTree (W.tree c) γ j)
      (cavityGeneratedObservedRawFutureFirstLeaf (W.tree c) γ j) τp)
    (observationTerminalSpin (cavityGeneratedObservedRawFutureTree (W.tree c) γ j)
      (cavityGeneratedObservedRawFutureSecondLeaf (W.tree c) γ j) τp) =
    cavitySpinOverlapDefect n z.2
      (cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j τp).2.1
      (cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j τp).2.2
  have hc := cavityGeneratedObservedRawFutureFreshLeaves_commonClock
    ((W.component c).clock (cavityGeneratedObservedRawFutureHistoryPrefix H))
    ((W.component c).clock_antitone _) (W.tree c) γ j
    (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark) hz.2.2.2
  refine (congrArg (fun q : Paper.Overlap => cavitySpinOverlapDefect n q
    (observationTerminalSpin (cavityGeneratedObservedRawFutureTree (W.tree c) γ j)
      (cavityGeneratedObservedRawFutureFirstLeaf (W.tree c) γ j) τp)
    (observationTerminalSpin (cavityGeneratedObservedRawFutureTree (W.tree c) γ j)
      (cavityGeneratedObservedRawFutureSecondLeaf (W.tree c) γ j) τp)) hc).trans ?_
  have hp := cavityGeneratedObservedRawFutureTerminalProject_pair (W.tree c) γ j τp
  have hl : H cavityGeneratedObservedRawFutureSecondMark = z.2 := by
    simp only [H,cavityGeneratedObservedRawFutureAppend,
      cavityGeneratedRawOriginFutureAppendedHistory,cavityGeneratedObservedRawFutureSecondMark,
      Fin.snoc_last]
  exact (congrArg (fun q : Paper.Overlap => cavitySpinOverlapDefect n q
    (observationTerminalSpin (cavityGeneratedObservedRawFutureTree (W.tree c) γ j)
      (cavityGeneratedObservedRawFutureFirstLeaf (W.tree c) γ j) τp)
    (observationTerminalSpin (cavityGeneratedObservedRawFutureTree (W.tree c) γ j)
      (cavityGeneratedObservedRawFutureSecondLeaf (W.tree c) γ j) τp)) hl).trans
    (congrArg (fun x => cavitySpinOverlapDefect n z.2 x.1 x.2) hp).symm

def cavityGeneratedObservedRawFutureTaggedTest (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c)) (A : CavityGeneratedObservedRawTaggedTest n W d) :
    CavityGeneratedObservedRawTaggedTest n (cavityGeneratedObservedRawFutureForest W c γ j) (d+1) where
  base := fun z => A.base
    (cavityGeneratedObservedRawFutureHistoryPrefix z.1,cavityGeneratedObservedRawFutureOldTerminal W c γ j z.2)
  pairs := Fin.snoc (fun i => cavityGeneratedObservedRawFuturePairMap W c γ j (A.pairs i))
    (cavityGeneratedObservedRawFutureFreshPair W c γ j)

theorem measurable_cavityGeneratedObservedRawFutureTaggedTest_base
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    Measurable (cavityGeneratedObservedRawFutureTaggedTest W c γ j A).base :=
  hA.comp ((measurable_cavityGeneratedObservedRawFutureHistoryPrefix.comp measurable_fst).prodMk
    ((measurable_of_finite (cavityGeneratedObservedRawFutureOldTerminal W c γ j)).comp measurable_snd))

theorem cavityGeneratedObservedRawFutureTaggedTest_base_bound
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (C : ℝ)
    (hA : ∀z, |A.base z| ≤ C) :
    ∀z, |(cavityGeneratedObservedRawFutureTaggedTest W c γ j A).base z| ≤ C := fun _ => hA _

theorem cavityGeneratedObservedRawFutureTaggedTest_source
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (A : CavityGeneratedObservedRawTaggedTest n W d)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedObservedRawFutureSourceEvent W c γ j)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawFutureForest W c γ j).depth
      (cavityGeneratedObservedRawFutureForest W c γ j).tree) :
    cavityGeneratedObservedRawFutureTerminalTest W c γ j (cavityGeneratedObservedRawTaggedValue W A)
      (cavityGeneratedObservedRawFutureAppend W c z) σ =
      cavityGeneratedObservedRawTaggedValue (cavityGeneratedObservedRawFutureForest W c γ j)
        (cavityGeneratedObservedRawFutureTaggedTest W c γ j A)
        (cavityGeneratedObservedRawFutureAppend W c z,σ) := by
  have he := cavityGeneratedObservedRawFutureFreshPair_defect W c γ j z hz σ
  have hp : (∏i : Fin d, cavityGeneratedObservedRawPairDefect W (A.pairs i) z.1.1
      (cavityGeneratedObservedRawFutureOldTerminal W c γ j σ)) =
      ∏i : Fin d, cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawFutureForest W c γ j)
        (cavityGeneratedObservedRawFuturePairMap W c γ j (A.pairs i))
        (cavityGeneratedObservedRawFutureAppend W c z) σ := by
    apply Finset.prod_congr rfl
    intro i _
    exact cavityGeneratedObservedRawFuturePairMap_defect W c γ j (A.pairs i) z hz σ
  simp only [cavityGeneratedObservedRawFutureTerminalTest,cavityGeneratedObservedRawTaggedValue,
    cavityGeneratedObservedRawFutureTaggedTest,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  have hl : cavityGeneratedObservedRawFutureAppend W c z cavityGeneratedObservedRawFutureSecondMark = z.2 := by
    simp only [cavityGeneratedObservedRawFutureAppend,cavityGeneratedRawOriginFutureAppendedHistory,
      cavityGeneratedObservedRawFutureSecondMark,Fin.snoc_last]
  rw [cavityGeneratedObservedRawFutureAppend_prefix,hl,←he,hp]
  exact mul_assoc _ _ _

end QuantitativeFollowup
