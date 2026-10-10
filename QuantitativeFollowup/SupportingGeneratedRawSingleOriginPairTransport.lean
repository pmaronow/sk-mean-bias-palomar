module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginSourceReceiverDefinitions

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

def cavityGeneratedObservedRawComponentLeafForward
    (U U' : CavityGeneratedObservedRawComponent m) (he : U=U')
    (i : ObservationLeaf U.tree) : ObservationLeaf U'.tree :=
  cavityGeneratedObservedRawComponentLeafCast U' U he.symm i

theorem cavityGeneratedObservedRawComponentLeafForward_spin
    (U U' : CavityGeneratedObservedRawComponent m) (he : U = U')
    (i : ObservationLeaf U.tree) (σ : CavityGeneratedObservedRawComponentTerminal n U') :
    observationTerminalSpin U.tree i
      ((cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U U' he).symm σ) =
    observationTerminalSpin U'.tree (cavityGeneratedObservedRawComponentLeafForward U U' he i) σ := by
  cases he
  rfl

theorem cavityGeneratedObservedRawComponentLeafForward_commonClock
    (U U' : CavityGeneratedObservedRawComponent m) (he : U = U')
    (H : CavityGeneratedHistory Paper.Overlap m) (i j : ObservationLeaf U.tree) :
    CavityGeneratedObservedRawComponent.clock U' H
      (observationCommonLevel U'.tree
        (cavityGeneratedObservedRawComponentLeafForward U U' he i)
        (cavityGeneratedObservedRawComponentLeafForward U U' he j)) =
    CavityGeneratedObservedRawComponent.clock U H (observationCommonLevel U.tree i j) := by
  cases he
  rfl

def cavityGeneratedObservedRawSingleOriginOldLeaf
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (i : Fin W.componentCount) (j : ObservationLeaf (W.tree i)) :
    ObservationLeaf ((cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree i) := by
  classical
  by_cases hi : i = c
  · subst i
    exact cavityGeneratedObservedRawComponentLeafForward
      (cavityGeneratedObservedRawChartComponent (W.component c) γ k)
      ((cavityGeneratedObservedRawSingleOriginChartForest W c γ k).component c)
      (cavityGeneratedObservedRawForestReplaceComponent_same (W.reindex Fin.castSucc) c _).symm
      (cavityGeneratedObservedRawChartOldLeaf (W.component c) γ k j)
  · exact cavityGeneratedObservedRawComponentLeafForward ((W.reindex Fin.castSucc).component i)
      ((cavityGeneratedObservedRawSingleOriginChartForest W c γ k).component i)
      (cavityGeneratedObservedRawForestReplaceComponent_other (W.reindex Fin.castSucc) c _ i hi).symm j

def cavityGeneratedObservedRawSingleOriginPairMap
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (t : CavityGeneratedObservedRawPair W) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawSingleOriginChartForest W c γ k) where
  component := t.component
  first := cavityGeneratedObservedRawSingleOriginOldLeaf W c γ k t.component t.first
  second := cavityGeneratedObservedRawSingleOriginOldLeaf W c γ k t.component t.second

def cavityGeneratedObservedRawSingleOriginOriginalFreshPair
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (i : ObservationLeaf (W.tree c)) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single) where
  component := c
  first := cavityGeneratedObservedRawSingleOriginOldLeaf W c γ .single c i
  second := cavityGeneratedObservedRawComponentLeafForward
    (cavityGeneratedObservedRawChartComponent (W.component c) γ .single)
    ((cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).component c)
    (cavityGeneratedObservedRawForestReplaceComponent_same (W.reindex Fin.castSucc) c _).symm
    (cavityGeneratedObservedRawChartFreshLeaf (W.component c) γ)

def cavityGeneratedObservedRawSingleOriginCurrentPair
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current) where
  component := c
  first := cavityGeneratedObservedRawComponentLeafForward
    (cavityGeneratedObservedRawChartComponent (W.component c) γ .current)
    ((cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).component c)
    (cavityGeneratedObservedRawForestReplaceComponent_same (W.reindex Fin.castSucc) c _).symm
    (cavityGeneratedObservedRawChartCurrentLeaf (W.component c) γ false)
  second := cavityGeneratedObservedRawComponentLeafForward
    (cavityGeneratedObservedRawChartComponent (W.component c) γ .current)
    ((cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).component c)
    (cavityGeneratedObservedRawForestReplaceComponent_same (W.reindex Fin.castSucc) c _).symm
    (cavityGeneratedObservedRawChartCurrentLeaf (W.component c) γ true)

theorem cavityGeneratedObservedRawComponentLeafForward_pair_defect
    (U U' : CavityGeneratedObservedRawComponent m) (he : U = U')
    (H : CavityGeneratedHistory Paper.Overlap m) (i j : ObservationLeaf U.tree)
    (σ : CavityGeneratedObservedRawComponentTerminal n U') :
    cavitySpinOverlapDefect n
      (CavityGeneratedObservedRawComponent.clock U H (observationCommonLevel U.tree i j))
      (observationTerminalSpin U.tree i
        ((cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U U' he).symm σ))
      (observationTerminalSpin U.tree j
        ((cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U U' he).symm σ)) =
    cavitySpinOverlapDefect n
      (CavityGeneratedObservedRawComponent.clock U' H
        (observationCommonLevel U'.tree (cavityGeneratedObservedRawComponentLeafForward U U' he i)
          (cavityGeneratedObservedRawComponentLeafForward U U' he j)))
      (observationTerminalSpin U'.tree (cavityGeneratedObservedRawComponentLeafForward U U' he i) σ)
      (observationTerminalSpin U'.tree (cavityGeneratedObservedRawComponentLeafForward U U' he j) σ) := by
  cases he
  rfl

theorem cavityGeneratedObservedRawSingleOriginOldTerminal_selected
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree) :
    cavityGeneratedObservedRawSingleOriginOldTerminal W c γ k σ c =
      (cavityGeneratedObservedRawSingleOriginSelectedProjection W c γ k σ).1 := by
  classical
  simp [cavityGeneratedObservedRawSingleOriginOldTerminal]

theorem cavityGeneratedObservedRawSingleOriginPairMap_defect
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (t : CavityGeneratedObservedRawPair W) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hr : cavityGeneratedObservedRawChartCell (W.component c) γ h r)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree) :
    cavityGeneratedObservedRawPairDefect W t h
      (cavityGeneratedObservedRawSingleOriginOldTerminal W c γ k σ) =
    cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawSingleOriginChartForest W c γ k)
      (cavityGeneratedObservedRawSingleOriginPairMap W c γ k t)
      (Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)) σ := by
  classical
  rcases t with ⟨i,f,s⟩
  let V := cavityGeneratedObservedRawSingleOriginChartForest W c γ k
  let U := cavityGeneratedObservedRawChartComponent (W.component c) γ k
  let H : CavityGeneratedHistory Paper.Overlap (m+1) := Fin.snoc h (cavityGeneratedObservedRawChartClock (W.component c) γ h r)
  by_cases hi : i=c
  · subst i
    have hp := cavityGeneratedObservedRawChartOldPair_defect (n:=n) (W.component c) γ k h r hr f s
      ((cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) (W.reindex Fin.castSucc) c U).symm (σ c))
    have hc := cavityGeneratedObservedRawComponentLeafForward_pair_defect (n:=n) U (V.component c)
      (cavityGeneratedObservedRawForestReplaceComponent_same (W.reindex Fin.castSucc) c U).symm H
      (cavityGeneratedObservedRawChartOldLeaf (W.component c) γ k f)
      (cavityGeneratedObservedRawChartOldLeaf (W.component c) γ k s) (σ c)
    unfold cavityGeneratedObservedRawPairDefect
    rw [cavityGeneratedObservedRawSingleOriginOldTerminal_selected]
    simpa [cavityGeneratedObservedRawSingleOriginPairMap,cavityGeneratedObservedRawSingleOriginOldLeaf,
      cavityGeneratedObservedRawSingleOriginSelectedProjection,V,U,H,
      cavityGeneratedObservedRawForestReplacementSelectedEquiv,
      CavityGeneratedObservedRawForest.tree,CavityGeneratedObservedRawForest.clock,
      CavityGeneratedObservedRawForest.depth] using hp.trans hc
  · have hc := cavityGeneratedObservedRawComponentLeafForward_pair_defect (n:=n) ((W.reindex Fin.castSucc).component i)
      (V.component i)
      (cavityGeneratedObservedRawForestReplaceComponent_other (W.reindex Fin.castSucc) c U i hi).symm H f s (σ i)
    have hclock : ((W.reindex Fin.castSucc).component i).clock H = W.clock h i := by
      change ((W.component i).reindex Fin.castSucc).clock H = (W.component i).clock h
      simpa only [H,Fin.snoc_castSucc] using (W.component i).reindex_clock Fin.castSucc H
    rw [hclock] at hc
    change cavitySpinOverlapDefect n
      (W.clock h i (observationCommonLevel (W.tree i) f s))
      (observationTerminalSpin (W.tree i) f _) (observationTerminalSpin (W.tree i) s _) = _ at hc
    simpa [cavityGeneratedObservedRawPairDefect,cavityGeneratedObservedRawSingleOriginPairMap,
      cavityGeneratedObservedRawSingleOriginOldLeaf,hi,cavityGeneratedObservedRawSingleOriginOldTerminal,
      cavityGeneratedObservedRawForestReplacementOtherEquiv,V,U,H,
      cavityGeneratedObservedRawSingleOriginChartForest,cavityGeneratedObservedRawForestReplaceComponent,
      CavityGeneratedObservedRawForest.tree,CavityGeneratedObservedRawForest.clock,
      CavityGeneratedObservedRawForest.depth] using hc

end QuantitativeFollowup
