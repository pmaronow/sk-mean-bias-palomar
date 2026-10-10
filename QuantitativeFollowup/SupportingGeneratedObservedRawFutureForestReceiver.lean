module
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureFamilies
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureTerminalReceiver
public import QuantitativeFollowup.SupportingGeneratedObservedRawForestReplacement

@[expose] public section

/-! The future terminal callback retains the arbitrary joint observable
of the complete original forest. Only its selected component is replaced;
all old coordinates are restored through the actual terminal projection. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def cavityGeneratedObservedRawFutureChosenTerminal (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawFutureForest W c γ j).depth
      (cavityGeneratedObservedRawFutureForest W c γ j).tree) :
    CavityGeneratedObservedRawComponentTerminal n (W.component c) ×
      (Configuration (n+1) × Configuration (n+1)) :=
  cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j
    ((cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n)
      (W.reindex (fun i => i.castSucc.castSucc)) c
      (cavityGeneratedObservedRawFutureComponent (W.component c) γ j)).symm (σ c))

def cavityGeneratedObservedRawFutureOldTerminal (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawFutureForest W c γ j).depth
      (cavityGeneratedObservedRawFutureForest W c γ j).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree := by
  classical
  exact fun i => if hi : i=c then
    cast (congrArg (fun s => CavityGeneratedObservedRawComponentTerminal n (W.component s)) hi.symm)
      (cavityGeneratedObservedRawFutureChosenTerminal W c γ j σ).1
    else (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n)
      (W.reindex (fun i => i.castSucc.castSucc)) c
      (cavityGeneratedObservedRawFutureComponent (W.component c) γ j) i hi).symm (σ i)

def cavityGeneratedObservedRawFutureTerminalTest (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawFutureForest W c γ j).depth
      (cavityGeneratedObservedRawFutureForest W c γ j).tree) : ℝ :=
  F (cavityGeneratedObservedRawFutureHistoryPrefix H,cavityGeneratedObservedRawFutureOldTerminal W c γ j σ) *
    cavitySpinOverlapDefect n (H cavityGeneratedObservedRawFutureSecondMark)
      (cavityGeneratedObservedRawFutureChosenTerminal W c γ j σ).2.1
      (cavityGeneratedObservedRawFutureChosenTerminal W c γ j σ).2.2

theorem cavityGeneratedObservedRawFutureTerminalProjection_replacement
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : CavityGeneratedObservedRawComponentTerminal n
      (cavityGeneratedObservedRawFutureComponent (W.component c) γ j)) :
    (cavityGeneratedObservedRawFutureOldTerminal W c γ j
      (cavityGeneratedObservedRawForestReplacementTerminal
        (W.reindex (fun i => i.castSucc.castSucc)) c
        (cavityGeneratedObservedRawFutureComponent (W.component c) γ j) σ τ),
      (cavityGeneratedObservedRawFutureChosenTerminal W c γ j
        (cavityGeneratedObservedRawForestReplacementTerminal
          (W.reindex (fun i => i.castSucc.castSucc)) c
          (cavityGeneratedObservedRawFutureComponent (W.component c) γ j) σ τ)).2) =
      (Function.update σ c (cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j τ).1,
        (cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j τ).2) := by
  classical
  let V := W.reindex (fun i => i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawFutureComponent (W.component c) γ j
  let y := cavityGeneratedObservedRawForestReplacementTerminal V c U σ τ
  have hp : cavityGeneratedObservedRawFutureChosenTerminal W c γ j y =
      cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j τ := by
    unfold cavityGeneratedObservedRawFutureChosenTerminal
    change cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j
      ((cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm
        (finiteProbabilityCoordinateReplacement c
          (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U)
          (σ,cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U τ) c)) = _
    rw [finiteProbabilityCoordinateReplacement_same,MeasurableEquiv.symm_apply_apply]
  have ho : cavityGeneratedObservedRawFutureOldTerminal W c γ j y =
      Function.update σ c (cavityGeneratedObservedRawFutureTerminalProject (W.tree c) γ j τ).1 := by
    funext i
    by_cases hi : i=c
    · subst i
      simp [cavityGeneratedObservedRawFutureOldTerminal,hp]
    · simp only [cavityGeneratedObservedRawFutureOldTerminal,dif_neg hi,
        Function.update_of_ne hi,y,U,V,cavityGeneratedObservedRawForestReplacementTerminal,
        finiteProbabilityCoordinateReplacement_other c _ _ i hi]
      exact (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U i hi).symm_apply_apply (σ i)
  change (cavityGeneratedObservedRawFutureOldTerminal W c γ j y,
    (cavityGeneratedObservedRawFutureChosenTerminal W c γ j y).2) = _
  rw [ho,hp]

theorem cavityGeneratedObservedRawFutureOrigin_decode (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedObservedRawFutureOrigin (W.tree c)
      (cavityGeneratedObservedRawFuturePayloadChart (W.tree c) z.2)
      (cavityGeneratedRawOriginSelectionClock (fun h => W.clock h c) (W.tree c) z) =
      cavityGeneratedOriginSelectionOrigin (W.tree c) z.2 := by
  rcases z with ⟨h,g⟩
  rcases g with i | (i | u) <;> rfl

def cavityGeneratedObservedRawFutureSourceValue (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) : ℝ :=
  ∫σ, nativeStreamingPatternMoment D μ a (W.clock z.1.1 c) (W.tree c)
    (fun τ => F (z.1.1,Function.update σ c τ))
    (.future (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2) j z.2)
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clock z.1.1) : Measure _)

theorem cavityGeneratedObservedRawFuture_forest_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) (hz : z ∈ cavityGeneratedObservedRawFutureSourceEvent W c γ j) :
    (∫σ, cavityGeneratedObservedRawFutureTerminalTest W c γ j F
      (cavityGeneratedObservedRawFutureAppend W c z) σ
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedObservedRawFutureForest W c γ j).depth
        (cavityGeneratedObservedRawFutureForest W c γ j).tree
        ((cavityGeneratedObservedRawFutureForest W c γ j).clock
          (cavityGeneratedObservedRawFutureAppend W c z)) : Measure _)) =
      cavityGeneratedObservedRawFutureSourceValue D μ a W c j F z := by
  let V := W.reindex (fun i => i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawFutureComponent (W.component c) γ j
  let H := cavityGeneratedObservedRawFutureAppend W c z
  have hprefix := cavityGeneratedObservedRawFutureAppend_prefix W c z
  have hfirst : H cavityGeneratedObservedRawFutureFirstMark =
      cavityGeneratedRawOriginSelectionClock (fun h => W.clock h c) (W.tree c) z.1 := by
    simp only [H,cavityGeneratedObservedRawFutureAppend,
      cavityGeneratedRawOriginFutureAppendedHistory,cavityGeneratedRawOriginAppendedHistory,
      cavityGeneratedObservedRawFutureFirstMark,Fin.snoc_castSucc,Fin.snoc_last]
  have horigin : cavityGeneratedObservedRawFutureOrigin (W.tree c) γ
      (H cavityGeneratedObservedRawFutureFirstMark) =
      cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2 := by
    rw [hfirst,←hz.2.1]
    exact cavityGeneratedObservedRawFutureOrigin_decode W c z.1
  have hlast : H cavityGeneratedObservedRawFutureSecondMark = z.2 := by
    simp only [H,cavityGeneratedObservedRawFutureAppend,
      cavityGeneratedRawOriginFutureAppendedHistory,cavityGeneratedObservedRawFutureSecondMark,
      Fin.snoc_last]
  change (∫σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawForestReplaceComponent V c U).depth
      (cavityGeneratedObservedRawForestReplaceComponent V c U).tree,
    cavityGeneratedObservedRawFutureTerminalTest W c γ j F H σ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a
      (cavityGeneratedObservedRawForestReplaceComponent V c U).depth
      (cavityGeneratedObservedRawForestReplaceComponent V c U).tree
      ((cavityGeneratedObservedRawForestReplaceComponent V c U).clock H) :
      Measure (CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedObservedRawForestReplaceComponent V c U).depth
        (cavityGeneratedObservedRawForestReplaceComponent V c U).tree))) = _
  rw [←integral_cavityGeneratedObservedRawForest_component_replacement D μ a V c U H
    (cavityGeneratedObservedRawFutureTerminalTest W c γ j F H)]
  have hVclock : V.clock H = W.clock z.1.1 := by
    change W.clock (cavityGeneratedObservedRawFutureHistoryPrefix H) = _
    rw [hprefix]
  rw [hVclock]
  apply integral_congr_ae
  refine .of_forall fun σ => ?_
  let γU : CavityGeneratedObservedRawOriginChart (W.component c).tree := γ
  let jU : Fin (W.component c).depth := j
  have horiginU : cavityGeneratedObservedRawFutureOrigin (W.component c).tree γU
      (H cavityGeneratedObservedRawFutureFirstMark) =
      cavityGeneratedOriginSelectionOrigin (W.component c).tree z.1.2 := horigin
  have ht := cavityGeneratedObservedRawFutureComponent_terminal_receiver D μ a (W.component c)
    γU jU H hz.2.2
    (fun x => F (z.1.1,Function.update σ c x.1) * cavitySpinOverlapDefect n z.2 x.2.1 x.2.2)
  rw [hprefix,horiginU,hlast] at ht
  refine Eq.trans ?_ ht
  apply integral_congr_ae
  refine .of_forall fun τ => ?_
  have he := cavityGeneratedObservedRawFutureTerminalProjection_replacement W c γ j σ τ
  change F (cavityGeneratedObservedRawFutureHistoryPrefix H,
    (cavityGeneratedObservedRawFutureOldTerminal W c γ j
      (cavityGeneratedObservedRawForestReplacementTerminal V c U σ τ))) *
      cavitySpinOverlapDefect n (H cavityGeneratedObservedRawFutureSecondMark)
        (cavityGeneratedObservedRawFutureChosenTerminal W c γ j
          (cavityGeneratedObservedRawForestReplacementTerminal V c U σ τ)).2.1
        (cavityGeneratedObservedRawFutureChosenTerminal W c γ j
          (cavityGeneratedObservedRawForestReplacementTerminal V c U σ τ)).2.2 = _
  rw [hprefix,hlast]
  exact congrArg (fun x : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1) × Configuration (n+1)) =>
    F (z.1.1,x.1) * cavitySpinOverlapDefect n z.2 x.2.1 x.2.2) he

end QuantitativeFollowup
