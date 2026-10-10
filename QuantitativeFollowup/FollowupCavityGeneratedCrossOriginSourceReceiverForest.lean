module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverTerminal
public import QuantitativeFollowup.FollowupCavityGeneratedForestJointLaw

@[expose] public section

/-! A cross receiver retains an arbitrary joint old-forest terminal test.
The selected component is replaced by its genuine enlarged cross tree;
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

def cavityGeneratedCrossOriginSelectedProjection
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) :
    CavityGeneratedComponentTerminal n (W.component c) × (Configuration (n+1) × Configuration (n+1)) :=
  printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k
    ((cavityGeneratedForestReplacementSelectedEquiv (n:=n)
      (W.reindex (fun i => i.castSucc.castSucc)) c
      (printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k)).symm (σ c))

def cavityGeneratedCrossOriginOldTerminal
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree := by
  classical
  exact fun i => if hi : i = c then
    cast (congrArg (fun d => CavityGeneratedComponentTerminal n (W.component d)) hi.symm)
      (cavityGeneratedCrossOriginSelectedProjection W c γ₁ γ₂ k σ).1
    else (cavityGeneratedForestReplacementOtherEquiv (n:=n)
      (W.reindex (fun d => d.castSucc.castSucc)) c
      (printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k) i hi).symm (σ i)

def cavityGeneratedCrossOriginTerminalProjection
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree × (Configuration (n+1) × Configuration (n+1)) :=
  (cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k σ,
    (cavityGeneratedCrossOriginSelectedProjection W c γ₁ γ₂ k σ).2)

theorem cavityGeneratedCrossOriginTerminalProjection_replacement
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : CavityGeneratedComponentTerminal n (printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k)) :
    cavityGeneratedCrossOriginTerminalProjection W c γ₁ γ₂ k
      (cavityGeneratedForestReplacementTerminal (W.reindex (fun i=>i.castSucc.castSucc)) c
        (printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k) σ τ) =
    (Function.update σ c (printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k τ).1,
      (printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k τ).2) := by
  classical
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k
  let y := cavityGeneratedForestReplacementTerminal V c U σ τ
  have hp : cavityGeneratedCrossOriginSelectedProjection W c γ₁ γ₂ k y =
      printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k τ := by
    unfold cavityGeneratedCrossOriginSelectedProjection
    change printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k
      ((cavityGeneratedForestReplacementSelectedEquiv (n:=n) V c U).symm
        (finiteProbabilityCoordinateReplacement c
          (cavityGeneratedForestReplacementOtherEquiv (n:=n) V c U)
          (σ,cavityGeneratedForestReplacementSelectedEquiv (n:=n) V c U τ) c)) = _
    rw [finiteProbabilityCoordinateReplacement_same,MeasurableEquiv.symm_apply_apply]
  have ho : cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k y =
      Function.update σ c (printedGeneratedOriginCrossChartTerminalProjection (W.component c) γ₁ γ₂ k τ).1 := by
    funext i
    by_cases hi : i=c
    · subst i
      simp [cavityGeneratedCrossOriginOldTerminal,hp]
    · simp only [cavityGeneratedCrossOriginOldTerminal,dif_neg hi,Function.update_of_ne hi,
        y,V,U,cavityGeneratedForestReplacementTerminal,
        finiteProbabilityCoordinateReplacement_other c _ _ i hi]
      exact (cavityGeneratedForestReplacementOtherEquiv (n:=n) V c U i hi).symm_apply_apply (σ i)
  change (cavityGeneratedCrossOriginOldTerminal W c γ₁ γ₂ k y,
    (cavityGeneratedCrossOriginSelectedProjection W c γ₁ γ₂ k y).2) = _
  rw [ho,hp]

theorem cavityGeneratedCrossOrigin_reindexed_terminal_law
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

private theorem cross_source_component_order
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

theorem cavityGeneratedCrossOrigin_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ₁ h r)
    (hl : printedGeneratedOriginChartCell (W.component c) γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds (W.component c) γ₁ γ₂ k r l)
    (G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ) :
    (∫σ, nativeStreamingTerminalMarkMoment
      (nativeStreamingOriginCrossProbability D μ a (W.clockTemplate.clock h c) (W.tree c)
        (printedGeneratedOriginCrossChartOrigin (W.component c) γ₁ r)
        (printedGeneratedOriginCrossChartOrigin (W.component c) γ₂ l))
      (fun z=>G (Function.update σ c z.1,z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    ∫σ,G (cavityGeneratedCrossOriginTerminalProjection W c γ₁ γ₂ k σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
        (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree
        ((cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).clockTemplate.clock
          (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l)) :
        Measure (CavityGeneratedForestTerminalSample (n:=n)
          (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
          (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree)) := by
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := printedGeneratedOriginCrossChartComponent (W.component c) γ₁ γ₂ k
  let H := printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l
  have hp := integral_cavityGeneratedForest_component_replacement D μ a V c U H
    (fun σ=>G (cavityGeneratedCrossOriginTerminalProjection W c γ₁ γ₂ k σ))
  change (∫σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree,
    ∫τ : CavityGeneratedComponentTerminal n U,
      G (cavityGeneratedCrossOriginTerminalProjection W c γ₁ γ₂ k
        (cavityGeneratedForestReplacementTerminal V c U σ τ))
      ∂cavityGeneratedComponentTerminalMeasure D μ a U H
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (V.clockTemplate.clock H) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) = _ at hp
  have hVclock : V.clockTemplate.clock H = W.clockTemplate.clock h := by
    funext d
    exact W.reindex_clock (fun i=>i.castSucc.castSucc) h H
      (fun i=>by simp only [H,printedGeneratedOriginCrossChartAppend,Fin.snoc_castSucc]) d
  rw [hVclock] at hp
  refine Eq.trans ?_ hp
  apply integral_congr_ae
  refine .of_forall fun σ=>?_
  have hc : W.clockTemplate.clock h c = nativeStreamingGeneratedComponentClock (W.component c) h :=
    printedGeneratedComponentClock_eq_native (W.component c) h
  have hlaw := printedGeneratedOriginCrossChart_terminal_receiver D μ a (W.component c) γ₁ γ₂ k h r l
    (cross_source_component_order W c h hh) hr hl hk
    (fun z=>G (Function.update σ c z.1,z.2))
  rw [←hc] at hlaw
  refine hlaw.symm.trans ?_
  apply integral_congr_ae
  exact .of_forall fun τ=>(congrArg G
    (cavityGeneratedCrossOriginTerminalProjection_replacement W c γ₁ γ₂ k σ τ)).symm

end QuantitativeFollowup
