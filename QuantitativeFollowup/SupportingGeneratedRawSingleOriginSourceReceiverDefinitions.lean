module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginFamilies
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginComponentLaw
public import QuantitativeFollowup.SupportingGeneratedObservedRawForestReplacement

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

def cavityGeneratedObservedRawSingleOriginSelectedProjection
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree) :
    CavityGeneratedObservedRawComponentTerminal n (W.component c) × k.Mark (Configuration (n+1)) :=
  cavityGeneratedObservedRawChartTerminalProject (W.component c) γ k
    ((cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) (W.reindex Fin.castSucc) c
      (cavityGeneratedObservedRawChartComponent (W.component c) γ k)).symm (σ c))

def cavityGeneratedObservedRawSingleOriginOldTerminal
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree := by
  classical
  exact fun i => if hi : i = c then
    cast (congrArg (fun j => CavityGeneratedObservedRawComponentTerminal n (W.component j)) hi.symm)
      (cavityGeneratedObservedRawSingleOriginSelectedProjection W c γ k σ).1
    else (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) (W.reindex Fin.castSucc) c
      (cavityGeneratedObservedRawChartComponent (W.component c) γ k) i hi).symm (σ i)

def cavityGeneratedObservedRawSingleOriginTerminalProjection
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree × k.Mark (Configuration (n+1)) :=
  (cavityGeneratedObservedRawSingleOriginOldTerminal W c γ k σ,
    (cavityGeneratedObservedRawSingleOriginSelectedProjection W c γ k σ).2)

theorem cavityGeneratedObservedRawSingleOriginTerminalProjection_replacement
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : CavityGeneratedObservedRawComponentTerminal n (cavityGeneratedObservedRawChartComponent (W.component c) γ k)) :
    cavityGeneratedObservedRawSingleOriginTerminalProjection W c γ k
      (cavityGeneratedObservedRawForestReplacementTerminal (W.reindex Fin.castSucc) c
        (cavityGeneratedObservedRawChartComponent (W.component c) γ k) σ τ) =
    (Function.update σ c (cavityGeneratedObservedRawChartTerminalProject (W.component c) γ k τ).1,
      (cavityGeneratedObservedRawChartTerminalProject (W.component c) γ k τ).2) := by
  classical
  let V := W.reindex Fin.castSucc
  let U := cavityGeneratedObservedRawChartComponent (W.component c) γ k
  let y := cavityGeneratedObservedRawForestReplacementTerminal V c U σ τ
  have hp : cavityGeneratedObservedRawSingleOriginSelectedProjection W c γ k y =
      cavityGeneratedObservedRawChartTerminalProject (W.component c) γ k τ := by
    unfold cavityGeneratedObservedRawSingleOriginSelectedProjection
    change cavityGeneratedObservedRawChartTerminalProject (W.component c) γ k
      ((cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm
        (finiteProbabilityCoordinateReplacement c
          (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U)
          (σ,cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U τ) c)) = _
    rw [finiteProbabilityCoordinateReplacement_same,MeasurableEquiv.symm_apply_apply]
  have ho : cavityGeneratedObservedRawSingleOriginOldTerminal W c γ k y =
      Function.update σ c (cavityGeneratedObservedRawChartTerminalProject (W.component c) γ k τ).1 := by
    funext i
    by_cases hi : i = c
    · subst i
      simp [cavityGeneratedObservedRawSingleOriginOldTerminal,hp]
    · simp only [cavityGeneratedObservedRawSingleOriginOldTerminal,dif_neg hi,Function.update_of_ne hi,
        y,V,U,cavityGeneratedObservedRawForestReplacementTerminal,
        finiteProbabilityCoordinateReplacement_other c _ _ i hi]
      exact (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U i hi).symm_apply_apply (σ i)
  change (cavityGeneratedObservedRawSingleOriginOldTerminal W c γ k y,
    (cavityGeneratedObservedRawSingleOriginSelectedProjection W c γ k y).2) = _
  rw [ho,hp]

theorem cavityGeneratedObservedRawSingleOrigin_reindexed_terminal_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) :
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth
      W.tree ((W.reindex Fin.castSucc).clock (Fin.snoc h r)) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) =
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) := by
  have hc : (W.reindex Fin.castSucc).clock (Fin.snoc h r) = W.clock h := by
    rw [W.reindex_clock]
    simp only [Fin.snoc_castSucc]
  rw [hc]

theorem cavityGeneratedObservedRawChartOrigin_clock
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) :
    cavityGeneratedObservedRawChartOrigin U γ (cavityGeneratedObservedRawChartClock U γ h r) =
      cavityGeneratedObservedRawChartOrigin U γ r := by
  rcases γ with i | (i | u) <;> rfl

theorem cavityGeneratedObservedRawForestSelectionOrigin_eq_chart
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (g : CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedOriginSelectionOrigin (W.tree c) g =
      cavityGeneratedObservedRawChartOrigin (W.component c)
        (cavityGeneratedObservedRawOriginPayloadChart (W.component c) g)
        (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) g) := by
  rcases g with i | (i | u) <;> rfl

def cavityGeneratedObservedRawSingleOriginOriginalFreshTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c))
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single).tree) : ℝ :=
  let z := cavityGeneratedObservedRawSingleOriginTerminalProjection W c γ .single σ
  F (cavityGeneratedHistoryPrefix H,z.1) * cavitySpinOverlapDefect n
    (nativeStreamingOriginCommonClock (W.clock (cavityGeneratedHistoryPrefix H) c)
      (W.tree c) (.vertex (observationLeafVertex (W.tree c) i))
      (cavityGeneratedObservedRawChartOrigin (W.component c) γ (H (Fin.last m))))
    (observationTerminalSpin (W.tree c) i (z.1 c)) z.2

def cavityGeneratedObservedRawSingleOriginCurrentTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current).tree) : ℝ :=
  let z := cavityGeneratedObservedRawSingleOriginTerminalProjection W c γ .current σ
  F (cavityGeneratedHistoryPrefix H,z.1) * cavitySpinOverlapDefect n
    (nativeStreamingOriginLevel (W.clock (cavityGeneratedHistoryPrefix H) c)
      (cavityGeneratedObservedRawChartOrigin (W.component c) γ (H (Fin.last m)))) z.2.1 z.2.2

def cavityGeneratedObservedRawSingleOriginBaseProjection
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedHistory Paper.Overlap (m+1) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).depth
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ k).tree →
    CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree :=
  fun z=>(cavityGeneratedHistoryPrefix z.1,cavityGeneratedObservedRawSingleOriginOldTerminal W c γ k z.2)

theorem measurable_cavityGeneratedObservedRawSingleOriginBaseProjection
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedVertexKind) :
    Measurable (cavityGeneratedObservedRawSingleOriginBaseProjection (n:=n) W c γ k) :=
  cavityGeneratedHistoryPrefix_measurable.prodMap
    (measurable_of_finite (cavityGeneratedObservedRawSingleOriginOldTerminal (n:=n) W c γ k))

end QuantitativeFollowup
