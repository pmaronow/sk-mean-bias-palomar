module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverForest

@[expose] public section

/-! The genuine enlarged cross-forest callback retains the original
history and an arbitrary joint observable of every original terminal. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def printedGeneratedOriginCrossChartSourceClock
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : Paper.Overlap :=
  nativeStreamingOriginCommonClock
    (nativeStreamingGeneratedComponentClock U (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H))) U.tree
    (printedGeneratedOriginCrossChartOrigin U γ₁ (H (Fin.last m).castSucc))
    (printedGeneratedOriginCrossChartOrigin U γ₂ (H (Fin.last (m+1))))

theorem measurable_printedGeneratedOriginCrossChartSourceClock
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U) :
    Measurable (printedGeneratedOriginCrossChartSourceClock U γ₁ γ₂) := by
  have hp : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
      cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)) :=
    cavityGeneratedHistoryPrefix_measurable.comp cavityGeneratedHistoryPrefix_measurable
  have hq (j : ℕ) : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
      nativeStreamingGeneratedComponentClock U (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)) j) :=
    (nativeStreamingGeneratedComponentClock_continuous U j).measurable.comp hp
  have hfirst : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
      H (Fin.last m).castSucc) := measurable_pi_apply _
  have hsecond : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
      H (Fin.last (m+1))) := measurable_pi_apply _
  have hVV (v w : FiniteCascadeRecordVertex U.tree) :
      Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
        nativeStreamingOriginCommonClock
          (nativeStreamingGeneratedComponentClock U (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)))
          U.tree (.vertex v) (.vertex w)) := hq _
  have hEV (e : NativeStreamingEdge U.tree) (v : FiniteCascadeRecordVertex U.tree)
      (f : CavityGeneratedHistory Paper.Overlap (m+2)→Paper.Overlap) (hf : Measurable f) :
      Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
        nativeStreamingOriginCommonClock
          (nativeStreamingGeneratedComponentClock U (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)))
          U.tree (.edge e (f H)) (.vertex v)) := by
    change Measurable (fun H=>if finiteCascadeCommonPathDepth U.tree v (nativeStreamingEdgeChildVertex e)=e.depth
      then f H else nativeStreamingGeneratedComponentClock U
        (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H))
        (finiteCascadeCommonPathDepth U.tree v (nativeStreamingEdgeChildVertex e)))
    split_ifs <;> first | exact hf | exact hq _
  have hVE (v : FiniteCascadeRecordVertex U.tree) (e : NativeStreamingEdge U.tree)
      (f : CavityGeneratedHistory Paper.Overlap (m+2)→Paper.Overlap) (hf : Measurable f) :
      Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
        nativeStreamingOriginCommonClock
          (nativeStreamingGeneratedComponentClock U (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)))
          U.tree (.vertex v) (.edge e (f H))) := hEV e v f hf
  have hEE (e f : NativeStreamingEdge U.tree) :
      Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
        nativeStreamingOriginCommonClock
          (nativeStreamingGeneratedComponentClock U (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)))
          U.tree (.edge e (H (Fin.last m).castSucc)) (.edge f (H (Fin.last (m+1))))) := by
    change Measurable (fun H=>nativeStreamingSelectedCommonClock
      (finiteCascadeCommonPathDepth U.tree (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f))
      e.depth f.depth (H (Fin.last m).castSucc) (H (Fin.last (m+1)))
      (nativeStreamingGeneratedComponentClock U (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H))
        (finiteCascadeCommonPathDepth U.tree (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f))))
    unfold nativeStreamingSelectedCommonClock
    split_ifs <;> first | exact hfirst | exact hsecond | exact hfirst.min hsecond | exact hq _
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  · exact hVV _ _
  · exact hVE _ _ _ hsecond
  · exact hVV _ _
  · exact hEV _ _ _ hfirst
  · exact hEE _ _
  · exact hEV _ _ _ hfirst
  · exact hVV _ _
  · exact hVE _ _ _ hsecond
  · exact hVV _ _

def cavityGeneratedCrossOriginTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) : ℝ :=
  let z := cavityGeneratedCrossOriginTerminalProjection W c γ₁ γ₂ k σ
  F (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H),z.1) *
    cavitySpinOverlapDefect n (printedGeneratedOriginCrossChartSourceClock (W.component c) γ₁ γ₂ H) z.2.1 z.2.2

theorem measurable_cavityGeneratedCrossOriginTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) (hF : Measurable F) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+2) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
        (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree =>
      cavityGeneratedCrossOriginTest W c γ₁ γ₂ k F z.1 z.2) := by
  classical
  apply measurable_from_prod_countable_left
  intro σ
  let z := cavityGeneratedCrossOriginTerminalProjection W c γ₁ γ₂ k σ
  have hp : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
      cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)) :=
    cavityGeneratedHistoryPrefix_measurable.comp cavityGeneratedHistoryPrefix_measurable
  have hval := hF.comp (hp.prodMk (measurable_const : Measurable (fun _ :
    CavityGeneratedHistory Paper.Overlap (m+2)=>z.1)))
  have hclock := measurable_printedGeneratedOriginCrossChartSourceClock (W.component c) γ₁ γ₂
  change Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+2)=>
    F (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H),z.1) *
      cavitySpinOverlapDefect n (printedGeneratedOriginCrossChartSourceClock (W.component c) γ₁ γ₂ H) z.2.1 z.2.2)
  exact hval.mul (measurable_const.sub
    (((measurable_subtype_coe.comp hclock).mul_const _).mul_const _))

theorem cavityGeneratedCrossOriginTest_abs_le
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀z,|F z|≤C)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).depth
      (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k).tree) :
    |cavityGeneratedCrossOriginTest W c γ₁ γ₂ k F H σ|≤2*C := by
  let z := cavityGeneratedCrossOriginTerminalProjection W c γ₁ γ₂ k σ
  change |F (_,z.1)*cavitySpinOverlapDefect n _ z.2.1 z.2.2|≤2*C
  rw [abs_mul]
  calc
    _ ≤ C*2 := mul_le_mul (hF _) (cavitySpinOverlapDefect_abs_le_two n
        (printedGeneratedOriginCrossChartSourceClock (W.component c) γ₁ γ₂ H)
        (printedGeneratedOriginCrossChartSourceClock (W.component c) γ₁ γ₂ H).property z.2.1 z.2.2)
      (abs_nonneg _) hC
    _ = _ := mul_comm _ _

def cavityGeneratedCrossOriginExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℝ :=
  ∫σ,cavityGeneratedCrossOriginTest W c γ₁ γ₂ k F H σ
    ∂cavityGeneratedForestTerminalKernel D μ a (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k) H

theorem measurable_cavityGeneratedCrossOriginExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) (hF : Measurable F) :
    Measurable (cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F) :=
  ((measurable_cavityGeneratedCrossOriginTest W c γ₁ γ₂ k F hF).stronglyMeasurable.integral_kernel_prod_right').measurable

theorem cavityGeneratedCrossOriginExpectation_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀z,|F z|≤C) (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    |cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F H|≤2*C := by
  simpa only [cavityGeneratedCrossOriginExpectation,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=cavityGeneratedForestTerminalKernel D μ a (cavityGeneratedCrossOriginChartForest W c γ₁ γ₂ k) H)
      (f:=fun σ=>cavityGeneratedCrossOriginTest W c γ₁ γ₂ k F H σ) (C:=2*C)
      (.of_forall fun σ=>by simpa only [Real.norm_eq_abs] using
        cavityGeneratedCrossOriginTest_abs_le W c γ₁ γ₂ k F C hC hF H σ)

theorem printedGeneratedOriginCrossChartOrigin_chartClock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) :
    printedGeneratedOriginCrossChartOrigin U γ (printedGeneratedOriginChartClock U γ h r) =
      printedGeneratedOriginCrossChartOrigin U γ r := by
  rcases γ with i | (i | u) <;> rfl

theorem cavityGeneratedCrossOrigin_cross_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈W.clockTemplate.orderSet)
    (hr : printedGeneratedOriginChartCell (W.component c) γ₁ h r)
    (hl : printedGeneratedOriginChartCell (W.component c) γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds (W.component c) γ₁ γ₂ k r l) :
    (∫σ,nativeStreamingPatternMoment D μ a (W.clockTemplate.clock h c) (W.tree c)
      (fun τ=>F (h,Function.update σ c τ))
      (.cross (printedGeneratedOriginCrossChartOrigin (W.component c) γ₁ r)
        (printedGeneratedOriginCrossChartOrigin (W.component c) γ₂ l))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clockTemplate.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F
      (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l) := by
  let G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      (Configuration (n+1)×Configuration (n+1)) → ℝ :=
    fun z=>F (h,z.1)*cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (W.clockTemplate.clock h c) (W.tree c)
        (printedGeneratedOriginCrossChartOrigin (W.component c) γ₁ r)
        (printedGeneratedOriginCrossChartOrigin (W.component c) γ₂ l)) z.2.1 z.2.2
  have hp := cavityGeneratedCrossOrigin_terminal_receiver D μ a W c γ₁ γ₂ k h r l hh hr hl hk G
  have hc : W.clockTemplate.clock h c = nativeStreamingGeneratedComponentClock (W.component c) h :=
    printedGeneratedComponentClock_eq_native (W.component c) h
  have hclock : printedGeneratedOriginCrossChartSourceClock (W.component c) γ₁ γ₂
      (printedGeneratedOriginCrossChartAppend (W.component c) γ₁ γ₂ h r l) =
      nativeStreamingOriginCommonClock (W.clockTemplate.clock h c) (W.tree c)
        (printedGeneratedOriginCrossChartOrigin (W.component c) γ₁ r)
        (printedGeneratedOriginCrossChartOrigin (W.component c) γ₂ l) := by
    simp only [printedGeneratedOriginCrossChartSourceClock,printedGeneratedOriginCrossChartAppend,
      cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last,Fin.snoc_castSucc,
      printedGeneratedOriginCrossChartOrigin_chartClock]
    rw [hc]
    rfl
  unfold cavityGeneratedCrossOriginExpectation cavityGeneratedCrossOriginTest
  rw [hclock]
  simpa only [G,nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,
    nativeStreamingDefectSpinTest,cavityGeneratedForestTerminalKernel_apply,
    printedGeneratedOriginCrossChartAppend,cavityGeneratedHistoryPrefix_snoc] using hp

end QuantitativeFollowup
