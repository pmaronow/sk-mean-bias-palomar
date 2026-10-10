module
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginFamilies
public import QuantitativeFollowup.SupportingGeneratedOriginComponentReceivers

@[expose] public section

/-! Whole-forest terminal tests for one selected original origin. The
selected component has an actual old-terminal/fresh-mark projection; all
other components are carried by the genuine replacement casts. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedSingleOriginSelectedProjection
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ k).depth
      (cavityGeneratedSingleOriginChartForest W c γ k).tree) :
    CavityGeneratedComponentTerminal n (W.component c) × k.Mark (Configuration (n+1)) :=
  printedGeneratedOriginChartTerminalProject (W.component c) γ k
    ((cavityGeneratedForestReplacementSelectedEquiv (n:=n) (W.reindex Fin.castSucc) c
      (printedGeneratedOriginChartComponent (W.component c) γ k)).symm (σ c))

def cavityGeneratedSingleOriginOldTerminal
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ k).depth
      (cavityGeneratedSingleOriginChartForest W c γ k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree := by
  classical
  exact fun i => if hi : i = c then
    cast (congrArg (fun j => CavityGeneratedComponentTerminal n (W.component j)) hi.symm)
      (cavityGeneratedSingleOriginSelectedProjection W c γ k σ).1
    else (cavityGeneratedForestReplacementOtherEquiv (n:=n) (W.reindex Fin.castSucc) c
      (printedGeneratedOriginChartComponent (W.component c) γ k) i hi).symm (σ i)

def cavityGeneratedSingleOriginTerminalProjection
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ k).depth
      (cavityGeneratedSingleOriginChartForest W c γ k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree × k.Mark (Configuration (n+1)) :=
  (cavityGeneratedSingleOriginOldTerminal W c γ k σ,
    (cavityGeneratedSingleOriginSelectedProjection W c γ k σ).2)

theorem cavityGeneratedSingleOriginTerminalProjection_replacement
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent (W.component c) γ k)) :
    cavityGeneratedSingleOriginTerminalProjection W c γ k
      (cavityGeneratedForestReplacementTerminal (W.reindex Fin.castSucc) c
        (printedGeneratedOriginChartComponent (W.component c) γ k) σ τ) =
    (Function.update σ c (printedGeneratedOriginChartTerminalProject (W.component c) γ k τ).1,
      (printedGeneratedOriginChartTerminalProject (W.component c) γ k τ).2) := by
  classical
  let V := W.reindex Fin.castSucc
  let U := printedGeneratedOriginChartComponent (W.component c) γ k
  let y := cavityGeneratedForestReplacementTerminal V c U σ τ
  have hp : cavityGeneratedSingleOriginSelectedProjection W c γ k y =
      printedGeneratedOriginChartTerminalProject (W.component c) γ k τ := by
    unfold cavityGeneratedSingleOriginSelectedProjection
    change printedGeneratedOriginChartTerminalProject (W.component c) γ k
      ((cavityGeneratedForestReplacementSelectedEquiv (n:=n) V c U).symm
        (finiteProbabilityCoordinateReplacement c
          (cavityGeneratedForestReplacementOtherEquiv (n:=n) V c U)
          (σ,cavityGeneratedForestReplacementSelectedEquiv (n:=n) V c U τ) c)) = _
    rw [finiteProbabilityCoordinateReplacement_same,MeasurableEquiv.symm_apply_apply]
  have ho : cavityGeneratedSingleOriginOldTerminal W c γ k y =
      Function.update σ c (printedGeneratedOriginChartTerminalProject (W.component c) γ k τ).1 := by
    funext i
    by_cases hi : i = c
    · subst i
      simp [cavityGeneratedSingleOriginOldTerminal,hp]
    · simp only [cavityGeneratedSingleOriginOldTerminal,dif_neg hi,Function.update_of_ne hi,
        y,V,U,cavityGeneratedForestReplacementTerminal,
        finiteProbabilityCoordinateReplacement_other c _ _ i hi]
      exact (cavityGeneratedForestReplacementOtherEquiv (n:=n) V c U i hi).symm_apply_apply (σ i)
  change (cavityGeneratedSingleOriginOldTerminal W c γ k y,
    (cavityGeneratedSingleOriginSelectedProjection W c γ k y).2) = _
  rw [ho,hp]

theorem cavityGeneratedSingleOrigin_reindexed_terminal_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) :
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth
      W.tree ((W.reindex Fin.castSucc).clockTemplate.clock (Fin.snoc h r)) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) =
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) := by
  have hc : (W.reindex Fin.castSucc).clockTemplate.clock (Fin.snoc h r) =
      W.clockTemplate.clock h := by
    funext c
    exact W.reindex_clock Fin.castSucc h (Fin.snoc h r)
      (fun i => by simp only [Fin.snoc_castSucc]) c
  change (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
    ((W.reindex Fin.castSucc).clockTemplate.clock (Fin.snoc h r)) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) = _
  rw [hc]

theorem cavityGeneratedOriginChartOrigin_clock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) :
    printedGeneratedOriginChartOrigin U γ (printedGeneratedOriginChartClock U γ h r) =
      printedGeneratedOriginChartOrigin U γ r := by
  rcases γ with i | (i | u) <;> rfl

theorem cavityGeneratedOriginSelectionOrigin_eq_chart
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (g : CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedOriginSelectionOrigin (W.tree c) g =
      printedGeneratedOriginChartOrigin (W.component c)
        (cavityGeneratedOriginPayloadChart (W.component c) g)
        (cavityGeneratedOriginPayloadFreeClock (W.component c) g) := by
  rcases g with i | (i | u) <;> rfl

def cavityGeneratedSingleOriginOriginalFreshTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c))
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedSingleOriginChartForest W c γ .single).tree) : ℝ :=
  let z := cavityGeneratedSingleOriginTerminalProjection W c γ .single σ
  F (cavityGeneratedHistoryPrefix H,z.1) * cavitySpinOverlapDefect n
    (nativeStreamingOriginCommonClock (W.clockTemplate.clock (cavityGeneratedHistoryPrefix H) c)
      (W.tree c) (.vertex (observationLeafVertex (W.tree c) i))
      (printedGeneratedOriginChartOrigin (W.component c) γ (H (Fin.last m))))
    (observationTerminalSpin (W.tree c) i (z.1 c)) z.2

def cavityGeneratedSingleOriginCurrentTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedSingleOriginChartForest W c γ .current).tree) : ℝ :=
  let z := cavityGeneratedSingleOriginTerminalProjection W c γ .current σ
  F (cavityGeneratedHistoryPrefix H,z.1) * cavitySpinOverlapDefect n
    (nativeStreamingOriginLevel (W.clockTemplate.clock (cavityGeneratedHistoryPrefix H) c)
      (printedGeneratedOriginChartOrigin (W.component c) γ (H (Fin.last m)))) z.2.1 z.2.2

end QuantitativeFollowup
