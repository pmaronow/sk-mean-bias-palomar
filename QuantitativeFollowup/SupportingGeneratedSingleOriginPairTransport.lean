module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTests
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginSourceReceiverDefinitions
public import QuantitativeFollowup.SupportingGeneratedSingleOriginNewPairs

@[expose] public section

/-! A single-origin successor transports all previous physical pair tags
through its actual whole-forest terminal projection, then appends the
chosen new leaf pair. Untouched components are retained jointly. -/
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

def cavityGeneratedComponentLeafCastEquiv
    (U U' : CavityGeneratedConstructedComponent m) (he : U = U') :
    ObservationLeaf U.tree ≃ ObservationLeaf U'.tree := by
  cases he
  exact Equiv.refl _

theorem cavityGeneratedComponentLeafCastEquiv_spin
    (U U' : CavityGeneratedConstructedComponent m) (he : U = U')
    (i : ObservationLeaf U.tree) (σ : CavityGeneratedComponentTerminal n U') :
    observationTerminalSpin U.tree i
      ((cavityGeneratedComponentTerminalCastEquiv (n:=n) U U' he).symm σ) =
    observationTerminalSpin U'.tree (cavityGeneratedComponentLeafCastEquiv U U' he i) σ := by
  cases he
  rfl

theorem cavityGeneratedComponentLeafCastEquiv_commonClock
    (U U' : CavityGeneratedConstructedComponent m) (he : U = U')
    (H : CavityGeneratedHistory Paper.Overlap m) (i j : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock U' H
      (observationCommonLevel U'.tree
        (cavityGeneratedComponentLeafCastEquiv U U' he i)
        (cavityGeneratedComponentLeafCastEquiv U U' he j)) =
    nativeStreamingGeneratedComponentClock U H (observationCommonLevel U.tree i j) := by
  cases he
  rfl

def cavityGeneratedSingleOriginOldLeaf
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (i : Fin W.componentCount) (j : ObservationLeaf (W.tree i)) :
    ObservationLeaf ((cavityGeneratedSingleOriginChartForest W c γ k).tree i) := by
  classical
  by_cases hi : i = c
  · subst i
    exact cavityGeneratedComponentLeafCastEquiv
      (printedGeneratedOriginChartComponent (W.component c) γ k)
      ((cavityGeneratedSingleOriginChartForest W c γ k).component c)
      (cavityGeneratedForestReplaceComponent_same (W.reindex Fin.castSucc) c _).symm
      (printedGeneratedOriginChartOldLeaf (W.component c) γ k j)
  · exact cavityGeneratedComponentLeafCastEquiv ((W.reindex Fin.castSucc).component i)
      ((cavityGeneratedSingleOriginChartForest W c γ k).component i)
      (cavityGeneratedForestReplaceComponent_other (W.reindex Fin.castSucc) c _ i hi).symm j

def cavityGeneratedSingleOriginPairMap
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (t : CavityGeneratedForestPair W) :
    CavityGeneratedForestPair (cavityGeneratedSingleOriginChartForest W c γ k) where
  component := t.component
  first := cavityGeneratedSingleOriginOldLeaf W c γ k t.component t.first
  second := cavityGeneratedSingleOriginOldLeaf W c γ k t.component t.second

def cavityGeneratedSingleOriginOriginalFreshPair
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (i : ObservationLeaf (W.tree c)) :
    CavityGeneratedForestPair (cavityGeneratedSingleOriginChartForest W c γ .single) where
  component := c
  first := cavityGeneratedSingleOriginOldLeaf W c γ .single c i
  second := cavityGeneratedComponentLeafCastEquiv
    (printedGeneratedOriginChartComponent (W.component c) γ .single)
    ((cavityGeneratedSingleOriginChartForest W c γ .single).component c)
    (cavityGeneratedForestReplaceComponent_same (W.reindex Fin.castSucc) c _).symm
    (printedGeneratedOriginChartFreshLeaf (W.component c) γ)

def cavityGeneratedSingleOriginCurrentPair
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) :
    CavityGeneratedForestPair (cavityGeneratedSingleOriginChartForest W c γ .current) where
  component := c
  first := cavityGeneratedComponentLeafCastEquiv
    (printedGeneratedOriginChartComponent (W.component c) γ .current)
    ((cavityGeneratedSingleOriginChartForest W c γ .current).component c)
    (cavityGeneratedForestReplaceComponent_same (W.reindex Fin.castSucc) c _).symm
    (printedGeneratedOriginChartCurrentLeaf (W.component c) γ false)
  second := cavityGeneratedComponentLeafCastEquiv
    (printedGeneratedOriginChartComponent (W.component c) γ .current)
    ((cavityGeneratedSingleOriginChartForest W c γ .current).component c)
    (cavityGeneratedForestReplaceComponent_same (W.reindex Fin.castSucc) c _).symm
    (printedGeneratedOriginChartCurrentLeaf (W.component c) γ true)

theorem cavityGeneratedComponentLeafCastEquiv_pair_defect
    (U U' : CavityGeneratedConstructedComponent m) (he : U = U')
    (H : CavityGeneratedHistory Paper.Overlap m) (i j : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n U') :
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock U H (observationCommonLevel U.tree i j))
      (observationTerminalSpin U.tree i
        ((cavityGeneratedComponentTerminalCastEquiv (n:=n) U U' he).symm σ))
      (observationTerminalSpin U.tree j
        ((cavityGeneratedComponentTerminalCastEquiv (n:=n) U U' he).symm σ)) =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock U' H
        (observationCommonLevel U'.tree (cavityGeneratedComponentLeafCastEquiv U U' he i)
          (cavityGeneratedComponentLeafCastEquiv U U' he j)))
      (observationTerminalSpin U'.tree (cavityGeneratedComponentLeafCastEquiv U U' he i) σ)
      (observationTerminalSpin U'.tree (cavityGeneratedComponentLeafCastEquiv U U' he j) σ) := by
  cases he
  rfl

theorem cavityGeneratedSingleOriginOldTerminal_selected
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ k).depth
      (cavityGeneratedSingleOriginChartForest W c γ k).tree) :
    cavityGeneratedSingleOriginOldTerminal W c γ k σ c =
      (cavityGeneratedSingleOriginSelectedProjection W c γ k σ).1 := by
  classical
  simp [cavityGeneratedSingleOriginOldTerminal]

theorem cavityGeneratedSingleOriginPairMap_defect
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (t : CavityGeneratedForestPair W) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ k).depth
      (cavityGeneratedSingleOriginChartForest W c γ k).tree) :
    cavityGeneratedForestPairDefect n W t h
      (cavityGeneratedSingleOriginOldTerminal W c γ k σ) =
    cavityGeneratedForestPairDefect n (cavityGeneratedSingleOriginChartForest W c γ k)
      (cavityGeneratedSingleOriginPairMap W c γ k t)
      (Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)) σ := by
  classical
  rcases t with ⟨i,f,s⟩
  let V := cavityGeneratedSingleOriginChartForest W c γ k
  let U := printedGeneratedOriginChartComponent (W.component c) γ k
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (printedGeneratedOriginChartClock (W.component c) γ h r)
  by_cases hi : i = c
  · subst i
    have hhU := (cavityGeneratedForest_orderSet_iff_components W h).mp hh c
    have hp := printedGeneratedOriginChartOldPair_defect (n:=n) (W.component c) γ k h r hhU hr f s
      ((cavityGeneratedForestReplacementSelectedEquiv (n:=n) (W.reindex Fin.castSucc) c U).symm (σ c))
    have hc := cavityGeneratedComponentLeafCastEquiv_pair_defect (n:=n) U (V.component c)
      (cavityGeneratedForestReplaceComponent_same (W.reindex Fin.castSucc) c U).symm H
      (printedGeneratedOriginChartOldLeaf (W.component c) γ k f)
      (printedGeneratedOriginChartOldLeaf (W.component c) γ k s) (σ c)
    change cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (W.component c) h
        (observationCommonLevel (W.tree c) f s))
      (observationTerminalSpin (W.tree c) f _) (observationTerminalSpin (W.tree c) s _) = _ at hp
    change _ = cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (V.component c) H
        (observationCommonLevel (V.tree c) _ _))
      (observationTerminalSpin (V.tree c) _ (σ c))
      (observationTerminalSpin (V.tree c) _ (σ c)) at hc
    unfold cavityGeneratedForestPairDefect
    rw [cavityGeneratedSingleOriginOldTerminal_selected]
    rw [←printedGeneratedComponentClock_of_forest W h c,printedGeneratedComponentClock_eq_native]
    change _ = cavitySpinOverlapDefect n (printedGeneratedComponentClock (V.component c) H _)
      (observationTerminalSpin _ _ (σ c)) (observationTerminalSpin _ _ (σ c))
    rw [printedGeneratedComponentClock_eq_native]
    simpa [cavityGeneratedSingleOriginPairMap,cavityGeneratedSingleOriginOldLeaf,
      cavityGeneratedSingleOriginSelectedProjection,V,U,H,
      cavityGeneratedForestReplacementSelectedEquiv] using hp.trans hc
  · have hc := cavityGeneratedComponentLeafCastEquiv_pair_defect (n:=n) ((W.reindex Fin.castSucc).component i)
      (V.component i)
      (cavityGeneratedForestReplaceComponent_other (W.reindex Fin.castSucc) c U i hi).symm H f s (σ i)
    change cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock ((W.reindex Fin.castSucc).component i) H
        (observationCommonLevel (W.tree i) f s))
      (observationTerminalSpin (W.tree i) f _) (observationTerminalSpin (W.tree i) s _) =
      cavitySpinOverlapDefect n (nativeStreamingGeneratedComponentClock (V.component i) H
        (observationCommonLevel (V.tree i) _ _))
      (observationTerminalSpin (V.tree i) _ (σ i))
      (observationTerminalSpin (V.tree i) _ (σ i)) at hc
    have hclock : nativeStreamingGeneratedComponentClock ((W.reindex Fin.castSucc).component i) H =
        W.clockTemplate.clock h i := by
      rw [←printedGeneratedComponentClock_eq_native,printedGeneratedComponentClock_of_forest]
      exact W.reindex_clock Fin.castSucc h H (fun j=>by simp only [H,Fin.snoc_castSucc]) i
    unfold cavityGeneratedForestPairDefect
    change _ = cavitySpinOverlapDefect n (printedGeneratedComponentClock (V.component i) H _)
      (observationTerminalSpin _ _ (σ i)) (observationTerminalSpin _ _ (σ i))
    rw [printedGeneratedComponentClock_eq_native]
    rw [hclock] at hc
    simpa [cavityGeneratedSingleOriginPairMap,cavityGeneratedSingleOriginOldLeaf,hi,
      cavityGeneratedSingleOriginOldTerminal,cavityGeneratedForestReplacementOtherEquiv,V,U,H,
      cavityGeneratedSingleOriginChartForest,cavityGeneratedForestReplaceComponent] using hc

end QuantitativeFollowup
