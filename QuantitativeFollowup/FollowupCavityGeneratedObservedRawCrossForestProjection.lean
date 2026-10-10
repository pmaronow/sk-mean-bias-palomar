module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossProjection

@[expose] public section

/-! The concrete cross forest projection retains every old terminal coordinate
and the ordered pair, including arbitrary joint tests. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def cavityGeneratedObservedRawCrossTerminalProjection
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree × (Configuration (n+1)×Configuration (n+1)) :=
  (cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ,
    (cavityGeneratedObservedRawCrossSelectedProjection W c γ δ k σ).2)

theorem cavityGeneratedObservedRawCrossTerminalProjection_replacement
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : CavityGeneratedObservedRawComponentTerminal n
      (cavityGeneratedObservedRawCrossComponent (W.component c)
        (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k)) :
    cavityGeneratedObservedRawCrossTerminalProjection W c γ δ k
      (cavityGeneratedObservedRawForestReplacementTerminal (W.reindex (fun i=>i.castSucc.castSucc)) c
        (cavityGeneratedObservedRawCrossComponent (W.component c)
          (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k) σ τ)=
      (Function.update σ c (cavityGeneratedRawCrossTerminalProjection (W.tree c)
          (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k τ).1,
        (cavityGeneratedRawCrossTerminalProjection (W.tree c)
          (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k τ).2) := by
  classical
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  let y := cavityGeneratedObservedRawForestReplacementTerminal V c U σ τ
  let p : CavityGeneratedObservedRawComponentTerminal n U →
      TerminalSpins (Configuration (n+1)) (W.tree c) × (Configuration (n+1)×Configuration (n+1)) :=
    cavityGeneratedRawCrossTerminalProjection (W.tree c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  have hp : cavityGeneratedObservedRawCrossSelectedProjection W c γ δ k y=p τ := by
    unfold cavityGeneratedObservedRawCrossSelectedProjection
    change p ((cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm
      (finiteProbabilityCoordinateReplacement c
        (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U)
        (σ,cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U τ) c))=_
    rw [finiteProbabilityCoordinateReplacement_same,MeasurableEquiv.symm_apply_apply]
  have ho : cavityGeneratedObservedRawCrossOldTerminal W c γ δ k y=Function.update σ c (p τ).1 := by
    funext i
    by_cases hi : i=c
    · subst i
      simp only [cavityGeneratedObservedRawCrossOldTerminal,dif_pos rfl,Function.update_self]
      exact congrArg Prod.fst hp
    · simp only [cavityGeneratedObservedRawCrossOldTerminal,dif_neg hi,Function.update_of_ne hi,
        y,V,U,cavityGeneratedObservedRawForestReplacementTerminal,
        finiteProbabilityCoordinateReplacement_other c _ _ i hi]
      exact (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U i hi).symm_apply_apply (σ i)
  change (cavityGeneratedObservedRawCrossOldTerminal W c γ δ k y,
    (cavityGeneratedObservedRawCrossSelectedProjection W c γ δ k y).2)=_
  rw [ho,hp]

theorem cavityGeneratedObservedRawCross_reindexed_clock
    (W : CavityGeneratedObservedRawForest m) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap) :
    (W.reindex (fun i=>i.castSucc.castSucc)).clock (cavityGeneratedRawCrossAppend h r l)=W.clock h := by
  funext c
  change (W.component c).clock (cavityGeneratedRawCrossPrefix (cavityGeneratedRawCrossAppend h r l))=_
  rw [cavityGeneratedRawCrossPrefix_append]
  rfl

end QuantitativeFollowup
