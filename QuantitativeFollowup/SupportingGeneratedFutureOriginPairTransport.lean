module
public import QuantitativeFollowup.SupportingGeneratedFutureOriginOldPairs
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTests

@[expose] public section

/-! The actual future operation preserves every old forest pair tag and
appends its literal new pair. Replacement casts retain untouched components;
the active source event supplies the genuine physical clock identities. -/
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

def futurePairLeafCast {M : ℕ} (U U' : CavityGeneratedConstructedComponent M)
    (he : U = U') (i : ObservationLeaf U.tree) : ObservationLeaf U'.tree :=
  cast (congrArg (fun V : CavityGeneratedConstructedComponent M => ObservationLeaf V.tree) he) i

private theorem futurePairLeafCast_defect {M : ℕ}
    (U U' : CavityGeneratedConstructedComponent M) (he : U = U')
    (h : CavityGeneratedHistory Paper.Overlap M) (i k : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n U') :
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock U' h
        (observationCommonLevel U'.tree (futurePairLeafCast U U' he i) (futurePairLeafCast U U' he k)))
      (observationTerminalSpin U'.tree (futurePairLeafCast U U' he i) σ)
      (observationTerminalSpin U'.tree (futurePairLeafCast U U' he k) σ) =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i k))
      (observationTerminalSpin U.tree i ((cavityGeneratedComponentTerminalCastEquiv (n:=n) U U' he).symm σ))
      (observationTerminalSpin U.tree k ((cavityGeneratedComponentTerminalCastEquiv (n:=n) U U' he).symm σ)) := by
  cases he
  rfl

private theorem futurePairForest_clock (W : CavityGeneratedConstructedForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    W.clockTemplate.clock h c = nativeStreamingGeneratedComponentClock (W.component c) h :=
  printedGeneratedComponentClock_eq_native (W.component c) h

def futurePairSelectedLeaf (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
    (j : Fin (W.depth c))
    (i : ObservationLeaf (printedGeneratedOriginFutureChartComponent (W.component c) γ j).tree) :
    ObservationLeaf ((cavityGeneratedFutureOriginChartForest W c γ j).tree c) :=
  futurePairLeafCast _ _
    (cavityGeneratedForestReplaceComponent_same (W.reindex (fun i=>i.castSucc.castSucc)) c
      (printedGeneratedOriginFutureChartComponent (W.component c) γ j)).symm i

def futurePairOldLeaf (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
    (j : Fin (W.depth c)) (i : Fin W.componentCount) (b : ObservationLeaf (W.tree i)) :
    ObservationLeaf ((cavityGeneratedFutureOriginChartForest W c γ j).tree i) := by
  classical
  by_cases hi : i = c
  · subst i
    exact futurePairSelectedLeaf W c γ j (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j b)
  · exact futurePairLeafCast _ _
      (cavityGeneratedForestReplaceComponent_other (W.reindex (fun i=>i.castSucc.castSucc)) c
        (printedGeneratedOriginFutureChartComponent (W.component c) γ j) i hi).symm b

def cavityGeneratedFutureOriginPairMap (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
    (j : Fin (W.depth c)) (t : CavityGeneratedForestPair W) :
    CavityGeneratedForestPair (cavityGeneratedFutureOriginChartForest W c γ j) where
  component := t.component
  first := futurePairOldLeaf W c γ j t.component t.first
  second := futurePairOldLeaf W c γ j t.component t.second

def cavityGeneratedFutureOriginFreshPair (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
    (j : Fin (W.depth c)) :
    CavityGeneratedForestPair (cavityGeneratedFutureOriginChartForest W c γ j) where
  component := c
  first := futurePairSelectedLeaf W c γ j (printedGeneratedOriginFutureChartFirstLeaf (W.component c) γ j)
  second := futurePairSelectedLeaf W c γ j (printedGeneratedOriginFutureChartSecondLeaf (W.component c) γ j)

private theorem futurePair_source_prefix
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (i : Fin m) :
    cavityGeneratedFutureOriginChartAppend W c z i.castSucc.castSucc = z.1.1 i := by
  simp only [cavityGeneratedFutureOriginChartAppend,nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_castSucc]

theorem cavityGeneratedFutureOriginPairMap_defect
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (t : CavityGeneratedForestPair W)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    cavityGeneratedForestPairDefect n W t z.1.1 (cavityGeneratedFutureOriginOldTerminal W c γ j σ) =
      cavityGeneratedForestPairDefect n (cavityGeneratedFutureOriginChartForest W c γ j)
        (cavityGeneratedFutureOriginPairMap W c γ j t) (cavityGeneratedFutureOriginChartAppend W c z) σ := by
  classical
  rcases t with ⟨i,b,e⟩
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginFutureChartComponent (W.component c) γ j
  let W' := cavityGeneratedFutureOriginChartForest W c γ j
  let H := cavityGeneratedFutureOriginChartAppend W c z
  by_cases hi : i = c
  · subst i
    let τ := cavityGeneratedFutureOriginChosenTerminal W c γ j σ
    have ho : cavityGeneratedFutureOriginOldTerminal W c γ j σ c =
        (printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j τ).1 := by
      simp only [cavityGeneratedFutureOriginOldTerminal,dif_pos rfl,cast_eq]
      rfl
    have hp := cavityGeneratedFutureOriginSource_oldPair_defect W c γ j z hz b e τ
    have he := futurePairLeafCast_defect U (W'.component c)
      (cavityGeneratedForestReplaceComponent_same V c U).symm H
      (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j b)
      (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j e) (σ c)
    have hn := futurePairForest_clock W' H c
    change cavitySpinOverlapDefect n
      (W.clockTemplate.clock z.1.1 c (observationCommonLevel (W.tree c) b e))
      (observationTerminalSpin (W.tree c) b (cavityGeneratedFutureOriginOldTerminal W c γ j σ c))
      (observationTerminalSpin (W.tree c) e (cavityGeneratedFutureOriginOldTerminal W c γ j σ c)) = _
    rw [ho,futurePairForest_clock W z.1.1 c]
    have hm : cavityGeneratedFutureOriginPairMap W c γ j ⟨c,b,e⟩ =
        (⟨c,
          futurePairLeafCast U (W'.component c) (cavityGeneratedForestReplaceComponent_same V c U).symm
            (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j b),
          futurePairLeafCast U (W'.component c) (cavityGeneratedForestReplaceComponent_same V c U).symm
            (printedGeneratedOriginFutureChartOldLeaf (W.component c) γ j e)⟩ : CavityGeneratedForestPair W') := by
      simp only [cavityGeneratedFutureOriginPairMap,futurePairOldLeaf,dif_pos rfl,dite_true]
      rfl
    rw [hm]
    change _ = cavitySpinOverlapDefect n (W'.clockTemplate.clock H c _) _ _
    rw [hn]
    exact hp.trans he.symm
  · have ho : cavityGeneratedFutureOriginOldTerminal W c γ j σ i =
        (cavityGeneratedForestReplacementOtherEquiv (n:=n) V c U i hi).symm (σ i) := by
      simp only [cavityGeneratedFutureOriginOldTerminal,dif_neg hi]
      rfl
    have hc : nativeStreamingGeneratedComponentClock (V.component i) H = W.clockTemplate.clock z.1.1 i := by
      rw [←futurePairForest_clock V H i]
      exact W.reindex_clock (fun i=>i.castSucc.castSucc) z.1.1 H
        (futurePair_source_prefix W c z) i
    have hn := futurePairForest_clock W' H i
    have he := futurePairLeafCast_defect (V.component i) (W'.component i)
      (cavityGeneratedForestReplaceComponent_other V c U i hi).symm H b e (σ i)
    change cavitySpinOverlapDefect n
      (W.clockTemplate.clock z.1.1 i (observationCommonLevel (W.tree i) b e))
      (observationTerminalSpin (W.tree i) b (cavityGeneratedFutureOriginOldTerminal W c γ j σ i))
      (observationTerminalSpin (W.tree i) e (cavityGeneratedFutureOriginOldTerminal W c γ j σ i)) = _
    rw [ho,←hc]
    have hm : cavityGeneratedFutureOriginPairMap W c γ j ⟨i,b,e⟩ =
        (⟨i,
          futurePairLeafCast (V.component i) (W'.component i)
            (cavityGeneratedForestReplaceComponent_other V c U i hi).symm b,
          futurePairLeafCast (V.component i) (W'.component i)
            (cavityGeneratedForestReplaceComponent_other V c U i hi).symm e⟩ : CavityGeneratedForestPair W') := by
      simp only [cavityGeneratedFutureOriginPairMap,futurePairOldLeaf,dif_neg hi]
      rfl
    rw [hm]
    change _ = cavitySpinOverlapDefect n (W'.clockTemplate.clock H i _) _ _
    rw [hn]
    exact he.symm

theorem cavityGeneratedFutureOriginFreshPair_defect
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    cavityGeneratedForestPairDefect n (cavityGeneratedFutureOriginChartForest W c γ j)
      (cavityGeneratedFutureOriginFreshPair W c γ j) (cavityGeneratedFutureOriginChartAppend W c z) σ =
    cavitySpinOverlapDefect n z.2 (cavityGeneratedFutureOriginSelectedProjection W c γ j σ).2.1
      (cavityGeneratedFutureOriginSelectedProjection W c γ j σ).2.2 := by
  unfold cavityGeneratedForestPairDefect
  simp only [cavityGeneratedFutureOriginFreshPair]
  rw [futurePairForest_clock]
  have he := futurePairLeafCast_defect _ _
    (cavityGeneratedForestReplaceComponent_same (W.reindex (fun i=>i.castSucc.castSucc)) c
      (printedGeneratedOriginFutureChartComponent (W.component c) γ j)).symm
    (cavityGeneratedFutureOriginChartAppend W c z)
    (printedGeneratedOriginFutureChartFirstLeaf (W.component c) γ j)
    (printedGeneratedOriginFutureChartSecondLeaf (W.component c) γ j) (σ c)
  exact he.trans (cavityGeneratedFutureOriginSource_freshPair_defect W c γ j z hz
    (cavityGeneratedFutureOriginChosenTerminal W c γ j σ)).symm

def cavityGeneratedFutureOriginTaggedTest (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
    (j : Fin (W.depth c)) (A : CavityGeneratedTaggedTest n W d) :
    CavityGeneratedTaggedTest n (cavityGeneratedFutureOriginChartForest W c γ j) (d+1) where
  base := fun z => A.base
    (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix z.1),
      cavityGeneratedFutureOriginOldTerminal W c γ j z.2)
  pairs := Fin.snoc (fun i => cavityGeneratedFutureOriginPairMap W c γ j (A.pairs i))
    (cavityGeneratedFutureOriginFreshPair W c γ j)

theorem cavityGeneratedFutureOriginTaggedTest_source
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (A : CavityGeneratedTaggedTest n W d)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hz : z ∈ cavityGeneratedFutureOriginChartSourceEvent W c γ j)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    cavityGeneratedFutureOriginTest W c γ j (cavityGeneratedTaggedTestValue W A)
      (cavityGeneratedFutureOriginChartAppend W c z) σ =
    cavityGeneratedTaggedTestValue (cavityGeneratedFutureOriginChartForest W c γ j)
      (cavityGeneratedFutureOriginTaggedTest W c γ j A) (cavityGeneratedFutureOriginChartAppend W c z,σ) := by
  have he := cavityGeneratedFutureOriginFreshPair_defect W c γ j z hz σ
  have hp : (∏i : Fin d,cavityGeneratedForestPairDefect n W (A.pairs i) z.1.1
      (cavityGeneratedFutureOriginOldTerminal W c γ j σ)) =
      ∏i : Fin d,cavityGeneratedForestPairDefect n (cavityGeneratedFutureOriginChartForest W c γ j)
        (cavityGeneratedFutureOriginPairMap W c γ j (A.pairs i))
        (cavityGeneratedFutureOriginChartAppend W c z) σ := by
    apply Finset.prod_congr rfl
    intro i _
    exact cavityGeneratedFutureOriginPairMap_defect W c γ j (A.pairs i) z hz σ
  simp only [cavityGeneratedFutureOriginTest,cavityGeneratedFutureOriginTerminalProjection,
    cavityGeneratedTaggedTestValue,cavityGeneratedFutureOriginTaggedTest,
    cavityGeneratedFutureOriginChartAppend,nativeStreamingGeneratedCrossEdgeAppend,
    cavityGeneratedHistoryPrefix_snoc,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  rw [←he,hp]
  exact mul_assoc _ _ _

end QuantitativeFollowup
