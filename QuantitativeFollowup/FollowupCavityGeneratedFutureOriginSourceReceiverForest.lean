module
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiverTerminal
public import QuantitativeFollowup.FollowupCavityGeneratedForestJointLaw

@[expose] public section

/-! A future receiver retains an arbitrary joint old-forest terminal test.
The selected component is replaced by its genuine enlarged future tree;
all untouched terminal coordinates retain their actual joint law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def cavityGeneratedFutureOriginSelectedProjection
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    CavityGeneratedComponentTerminal n (W.component c) × (Configuration (n+1) × Configuration (n+1)) :=
  printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j
    ((cavityGeneratedForestReplacementSelectedEquiv (n:=n)
      (W.reindex (fun i => i.castSucc.castSucc)) c
      (printedGeneratedOriginFutureChartComponent (W.component c) γ j)).symm (σ c))

def cavityGeneratedFutureOriginOldTerminal
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree := by
  classical
  exact fun i => if hi : i = c then
    cast (congrArg (fun d => CavityGeneratedComponentTerminal n (W.component d)) hi.symm)
      (cavityGeneratedFutureOriginSelectedProjection W c γ j σ).1
    else (cavityGeneratedForestReplacementOtherEquiv (n:=n)
      (W.reindex (fun d => d.castSucc.castSucc)) c
      (printedGeneratedOriginFutureChartComponent (W.component c) γ j) i hi).symm (σ i)

def cavityGeneratedFutureOriginTerminalProjection
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree × (Configuration (n+1) × Configuration (n+1)) :=
  (cavityGeneratedFutureOriginOldTerminal W c γ j σ,
    (cavityGeneratedFutureOriginSelectedProjection W c γ j σ).2)

theorem cavityGeneratedFutureOriginTerminalProjection_replacement
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent (W.component c) γ j)) :
    cavityGeneratedFutureOriginTerminalProjection W c γ j
      (cavityGeneratedForestReplacementTerminal (W.reindex (fun i=>i.castSucc.castSucc)) c
        (printedGeneratedOriginFutureChartComponent (W.component c) γ j) σ τ) =
    (Function.update σ c (printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j τ).1,
      (printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j τ).2) := by
  classical
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginFutureChartComponent (W.component c) γ j
  let y := cavityGeneratedForestReplacementTerminal V c U σ τ
  have hp : cavityGeneratedFutureOriginSelectedProjection W c γ j y =
      printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j τ := by
    unfold cavityGeneratedFutureOriginSelectedProjection
    change printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j
      ((cavityGeneratedForestReplacementSelectedEquiv (n:=n) V c U).symm
        (finiteProbabilityCoordinateReplacement c
          (cavityGeneratedForestReplacementOtherEquiv (n:=n) V c U)
          (σ,cavityGeneratedForestReplacementSelectedEquiv (n:=n) V c U τ) c)) = _
    rw [finiteProbabilityCoordinateReplacement_same,MeasurableEquiv.symm_apply_apply]
  have ho : cavityGeneratedFutureOriginOldTerminal W c γ j y =
      Function.update σ c (printedGeneratedFutureOriginChartTerminalProject (W.component c) γ j τ).1 := by
    funext i
    by_cases hi : i=c
    · subst i
      simp [cavityGeneratedFutureOriginOldTerminal,hp]
    · simp only [cavityGeneratedFutureOriginOldTerminal,dif_neg hi,Function.update_of_ne hi,
        y,V,U,cavityGeneratedForestReplacementTerminal,
        finiteProbabilityCoordinateReplacement_other c _ _ i hi]
      exact (cavityGeneratedForestReplacementOtherEquiv (n:=n) V c U i hi).symm_apply_apply (σ i)
  change (cavityGeneratedFutureOriginOldTerminal W c γ j y,
    (cavityGeneratedFutureOriginSelectedProjection W c γ j y).2) = _
  rw [ho,hp]

theorem cavityGeneratedFutureOrigin_reindexed_terminal_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap) :
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      ((W.reindex (fun i=>i.castSucc.castSucc)).clockTemplate.clock
        (nativeStreamingGeneratedCrossEdgeAppend h r l)) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) =
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) := by
  have hc : (W.reindex (fun i=>i.castSucc.castSucc)).clockTemplate.clock
      (nativeStreamingGeneratedCrossEdgeAppend h r l) = W.clockTemplate.clock h := by
    funext c
    exact W.reindex_clock (fun i=>i.castSucc.castSucc) h
      (nativeStreamingGeneratedCrossEdgeAppend h r l)
      (fun i=>by simp only [nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_castSucc]) c
  change (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
    ((W.reindex (fun i=>i.castSucc.castSucc)).clockTemplate.clock
      (nativeStreamingGeneratedCrossEdgeAppend h r l)) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) = _
  rw [hc]

private theorem future_source_component_order
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈W.clockTemplate.orderSet) :
    h∈nativeStreamingGeneratedComponentOrderSet (W.component c) := by
  intro j
  have he (p : ℕ) :
      (cavityGeneratedFiniteClockLabels (W.component c).label p).value h =
        W.clockTemplate.rawClock h c p := by
    by_cases hp : p≤W.depth c
    · simp only [cavityGeneratedFiniteClockLabels,CavityGeneratedConstructedForest.component,
        CavityGeneratedConstructedForest.clockTemplate,CavityGeneratedForestClockTemplate.rawClock,dif_pos hp]
    · simp only [cavityGeneratedFiniteClockLabels,CavityGeneratedConstructedForest.component,
        CavityGeneratedConstructedForest.clockTemplate,CavityGeneratedForestClockTemplate.rawClock,
        dif_neg hp,CavityGeneratedClockLabel.value]
  simpa only [he] using hh c j

theorem cavityGeneratedFutureOrigin_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ h r)
    (hl : nativeStreamingGeneratedComponentClock (W.component c) h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock (W.component c) h j)
    (hfuture : printedGeneratedOriginChartClock (W.component c) γ h r < l)
    (G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ) :
    (∫σ, nativeStreamingTerminalMarkMoment
      (nativeStreamingOriginFutureProbability D μ a (W.clockTemplate.clock h c) (W.tree c)
        (printedGeneratedFutureOriginChartOrigin (W.component c) γ r) j l)
      (fun z=>G (Function.update σ c z.1,z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    ∫σ,G (cavityGeneratedFutureOriginTerminalProjection W c γ j σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedFutureOriginChartForest W c γ j).depth
        (cavityGeneratedFutureOriginChartForest W c γ j).tree
        ((cavityGeneratedFutureOriginChartForest W c γ j).clockTemplate.clock
          (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock (W.component c) γ h r) l)) :
        Measure (CavityGeneratedForestTerminalSample (n:=n)
          (cavityGeneratedFutureOriginChartForest W c γ j).depth
          (cavityGeneratedFutureOriginChartForest W c γ j).tree)) := by
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginFutureChartComponent (W.component c) γ j
  let H := nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock (W.component c) γ h r) l
  have hp := integral_cavityGeneratedForest_component_replacement D μ a V c U H
    (fun σ=>G (cavityGeneratedFutureOriginTerminalProjection W c γ j σ))
  have hVclock : V.clockTemplate.clock H = W.clockTemplate.clock h := by
    funext d
    exact W.reindex_clock (fun i=>i.castSucc.castSucc) h H
      (fun i=>by simp only [H,nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_castSucc]) d
  rw [hVclock] at hp
  refine Eq.trans ?_ hp
  apply integral_congr_ae
  refine .of_forall fun σ=>?_
  have hc : W.clockTemplate.clock h c = nativeStreamingGeneratedComponentClock (W.component c) h :=
    printedGeneratedComponentClock_eq_native (W.component c) h
  have hlaw := printedGeneratedFutureOriginChart_terminal_receiver D μ a (W.component c) γ j h r l
    (future_source_component_order W c h hh) hr hl hfuture
    (fun z=>G (Function.update σ c z.1,z.2))
  rw [←hc] at hlaw
  refine hlaw.symm.trans ?_
  apply integral_congr_ae
  exact .of_forall fun τ=>(congrArg G
    (cavityGeneratedFutureOriginTerminalProjection_replacement W c γ j σ τ)).symm

end QuantitativeFollowup
