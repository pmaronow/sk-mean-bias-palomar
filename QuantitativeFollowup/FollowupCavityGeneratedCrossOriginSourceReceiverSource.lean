module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverMeasurable
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginChartCoverage

@[expose] public section

/-! Exact chart receivers preserve both selected origins from the
original component, and transport the full joint old-forest observable. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem printedGeneratedCrossSelectionOrigin_eq_chart
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (g : CavityGeneratedOriginSelection (W.tree c)) :
    cavityGeneratedOriginSelectionOrigin (W.tree c) g =
      printedGeneratedOriginCrossChartOrigin (W.component c)
        (cavityGeneratedOriginPayloadChart (W.component c) g)
        (cavityGeneratedOriginPayloadFreeClock (W.component c) g) := by
  rcases g with i | (i | u) <;> rfl

def cavityGeneratedCrossOriginSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedCrossOriginPayload W c) : ℝ :=
  ∫σ,nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1.1 c) (W.tree c)
    (fun τ=>F (z.1.1,Function.update σ c τ))
    (.cross (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2)
      (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
    ∂cavityGeneratedForestTerminalKernel D μ a W z.1.1

theorem cavityGeneratedCrossOrigin_source_event_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedCrossOriginPayload W c)
    (hz : z∈cavityGeneratedCrossOriginChartEvent W c γ₁ γ₂ k) :
    cavityGeneratedCrossOriginSourceValue D μ a W c F z =
      cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F
        (cavityGeneratedCrossOriginAppend W c z) := by
  rw [cavityGeneratedCrossOriginChartEvent_eq] at hz
  have hγ : cavityGeneratedOriginPayloadChart (W.component c) z.1.2=γ₁ := hz.1.1
  have hδ : cavityGeneratedOriginPayloadChart (W.component c) z.2=γ₂ := hz.2.1.1
  have ho₁ : cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2 =
      printedGeneratedOriginCrossChartOrigin (W.component c) γ₁
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2) := by
    rw [printedGeneratedCrossSelectionOrigin_eq_chart,hγ]
  have ho₂ : cavityGeneratedOriginSelectionOrigin (W.tree c) z.2 =
      printedGeneratedOriginCrossChartOrigin (W.component c) γ₂
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    rw [printedGeneratedCrossSelectionOrigin_eq_chart,hδ]
  have ht₁ : cavityGeneratedOriginSelectionClock W c z.1 =
      printedGeneratedOriginChartClock (W.component c) γ₁ z.1.1
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2) := by
    rw [cavityGeneratedOriginSelectionClock_eq_chart,hγ]
  have ht₂ : cavityGeneratedOriginSecondSelectionClock W c z =
      printedGeneratedOriginChartClock (W.component c) γ₂ z.1.1
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    change cavityGeneratedOriginSelectionClock W c (z.1.1,z.2)=_
    rw [cavityGeneratedOriginSelectionClock_eq_chart,hδ]
  have hk : printedGeneratedOriginCrossChartHolds (W.component c) γ₁ γ₂ k
      (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2)
      (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
    all_goals try trivial
    exact hz.2.2
  unfold cavityGeneratedCrossOriginSourceValue cavityGeneratedCrossOriginAppend
  rw [ho₁,ho₂,ht₁,ht₂]
  exact cavityGeneratedCrossOrigin_cross_receiver D μ a W c γ₁ γ₂ k F z.1.1
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2)
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2)
    hz.1.2.1 hz.1.2.2 hz.2.1.2.2 hk

theorem cavityGeneratedCrossOriginChart_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ₁ γ₂ : PrintedGeneratedOriginChart (W.component c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) (hF : Measurable F) :
    (∫H,cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F H
      ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ₁ γ₂ k) =
      ∫z,cavityGeneratedCrossOriginSourceValue D μ a W c F z
        ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
          (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst).restrict
            (cavityGeneratedCrossOriginChartEvent W c γ₁ γ₂ k) := by
  rw [cavityGeneratedCrossOriginChartMeasure,integral_map
    (measurable_cavityGeneratedCrossOriginAppend W c).aemeasurable
    (measurable_cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F hF).aestronglyMeasurable]
  apply integral_congr_ae
  exact (ae_restrict_mem (measurableSet_cavityGeneratedCrossOriginChartEvent W c γ₁ γ₂ k)).mono
    (fun z hz=>(cavityGeneratedCrossOrigin_source_event_receiver D μ a W c γ₁ γ₂ k F z hz).symm)

theorem cavityGeneratedCrossOrigin_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (cavityGeneratedCrossOriginSourceValue D μ a W c F)
      ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
        (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst) ∧
    (∑γ₁,∑γ₂,∑k,
      ∫H,cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F H
        ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ₁ γ₂ k) =
      ∫z,cavityGeneratedCrossOriginSourceValue D μ a W c F z
        ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
          (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst) := by
  classical
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  let N := (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
    (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst
  let G := PrintedGeneratedOriginChart (W.component c) ×
    (PrintedGeneratedOriginChart (W.component c) × NativeStreamingGeneratedCrossEdgeChart)
  let E := fun s : G=>cavityGeneratedCrossOriginChartEvent W c s.1 s.2.1 s.2.2
  let f := cavityGeneratedCrossOriginSourceValue D μ a W c F
  have hE s : MeasurableSet (E s) := measurableSet_cavityGeneratedCrossOriginChartEvent W c _ _ _
  have hp : (∑s : G,N.restrict (E s))=N :=
    finiteMeasureChartPartition_sum_restrict N E hE
      (cavityGeneratedCrossOriginChartEvent_disjoint W c)
      (by
        filter_upwards [cavityGeneratedCrossOriginChartEvent_cover_ae μ a W c M horder] with z hz
        rcases hz with ⟨γ₁,γ₂,k,hk⟩
        exact ⟨(γ₁,γ₂,k),hk⟩)
  have his (s : G) : Integrable f (N.restrict (E s)) := by
    have hi : Integrable (fun z=>cavityGeneratedCrossOriginExpectation D μ a W c s.1 s.2.1 s.2.2 F
        (cavityGeneratedCrossOriginAppend W c z)) (N.restrict (E s)) :=
      (integrable_const (2*C)).mono'
        (((measurable_cavityGeneratedCrossOriginExpectation D μ a W c _ _ _ F hF).comp
          (measurable_cavityGeneratedCrossOriginAppend W c)).aestronglyMeasurable)
        (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using
          cavityGeneratedCrossOriginExpectation_abs_le D μ a W c _ _ _ F C hC hbound _)
    exact hi.congr ((ae_restrict_mem (hE s)).mono fun z hz=>
      (cavityGeneratedCrossOrigin_source_event_receiver D μ a W c _ _ _ F z hz).symm)
  have hi : Integrable f N := by
    rw [←hp]
    exact integrable_finsetSum_measure.mpr (fun s _=>his s)
  refine ⟨hi,?_⟩
  have hsum : (∑s : G,∫H,cavityGeneratedCrossOriginExpectation D μ a W c s.1 s.2.1 s.2.2 F H
      ∂cavityGeneratedCrossOriginChartMeasure μ a W c M s.1 s.2.1 s.2.2) =∫z,f z ∂N := by
    calc
      _ =∑s : G,∫z,f z ∂N.restrict (E s) := by
        apply Finset.sum_congr rfl
        intro s _
        exact cavityGeneratedCrossOriginChart_source_receiver D μ a W c M _ _ _ F hF
      _ =∫z,f z ∂(∑s : G,N.restrict (E s)) :=
        (integral_finsetSum_measure (fun s _=>his s)).symm
      _ =_ := by rw [hp]
  simpa only [G,Fintype.sum_prod_type,N,f] using hsum

end QuantitativeFollowup
