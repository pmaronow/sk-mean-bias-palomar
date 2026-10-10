module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedStepSourceCoverageDefinitions

@[expose] public section

/-! Each genuine source-family terminal integral is the corresponding
literal successor tagged integral. Chart support is derived from the
actual restricted pushforward measures, retaining every old pair. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m d : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem measurable_projectedBase {X Y S R : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace R]
    [Countable S] [MeasurableSingletonClass S]
    (B : Y × R → ℝ) (hB : Measurable B) (π : X → Y) (hπ : Measurable π) (τ : S → R) :
    Measurable (fun z : X × S => B (π z.1,τ z.2)) := by
  apply measurable_from_prod_countable_left
  intro σ
  change Measurable (fun x : X => B (π x,τ σ))
  exact hB.comp (hπ.prodMk (measurable_const (a:=τ σ)))

theorem measurable_cavityGeneratedTaggedTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (A : CavityGeneratedTaggedTest n W d)
    (hA : Measurable A.base) :
    Measurable (cavityGeneratedTaggedTerminalExpectation D μ a W A) :=
  ((measurable_cavityGeneratedTaggedTestValue W A hA).stronglyMeasurable.integral_kernel_prod_right'
    (κ := cavityGeneratedForestTerminalKernel D μ a W)).measurable

private theorem expectation_ae_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Measure X) (S : Set X) (hS : MeasurableSet S)
    (π : X → Y) (hπ : Measurable π) (f g : Y → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀x∈S,f (π x)=g (π x)) :
    ∀ᵐy ∂(M.restrict S).map π,f y=g y := by
  apply (ae_map_iff hπ.aemeasurable (measurableSet_eq_fun hf hg)).mpr
  exact (ae_restrict_mem hS).mono (fun x hx=>he x hx)

theorem cavityGeneratedTaggedOriginalExpectation
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c)) (A : CavityGeneratedTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedStreamingOriginalExpectation D μ a W c i k (cavityGeneratedTaggedTestValue W A) h =
      cavityGeneratedTaggedTerminalExpectation D μ a W (cavityGeneratedOriginalTaggedTest W c i k A) h := by
  apply integral_congr_ae
  exact .of_forall fun σ=>cavityGeneratedOriginalTaggedTest_receiver hn W c i k A h σ

theorem cavityGeneratedTaggedNormalizerExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (A : CavityGeneratedTaggedTest n W d)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    printedGeneratedNormalizerSourceExpectation D μ a W
      (fun h σ=>cavityGeneratedTaggedTestValue W A (h,σ)) H =
      cavityGeneratedTaggedTerminalExpectation D μ a (printedGeneratedNormalizerAppendedForest W)
        (printedGeneratedNormalizerTaggedSuccessor W A) H := by
  rw [printedGeneratedNormalizerSourceExpectation_pair_test]
  apply integral_congr_ae
  exact .of_forall fun σ=>(printedGeneratedNormalizerTaggedSuccessor_value W A H σ).symm

private theorem singleOriginalFresh_ae
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (i : ObservationLeaf (W.tree c))
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base) :
    ∀ᵐH ∂cavityGeneratedSingleOriginChartMeasure μ a W c M γ,
      cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ (cavityGeneratedTaggedTestValue W A) i H =
      cavityGeneratedTaggedTerminalExpectation D μ a (cavityGeneratedSingleOriginChartForest W c γ .single)
        (cavityGeneratedSingleOriginOriginalFreshTaggedTest W c γ i A) H := by
  have hb : Measurable (cavityGeneratedSingleOriginOriginalFreshTaggedTest W c γ i A).base :=
    measurable_projectedBase A.base hA cavityGeneratedHistoryPrefix
      cavityGeneratedHistoryPrefix_measurable (cavityGeneratedSingleOriginOldTerminal W c γ .single)
  unfold cavityGeneratedSingleOriginChartMeasure
  apply expectation_ae_map _ _ (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ)
    _ (cavityGeneratedSingleOriginChart_append_measurable W c) _ _
    (measurable_cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ _
      (measurable_cavityGeneratedTaggedTestValue W A hA) i)
    (measurable_cavityGeneratedTaggedTerminalExpectation D μ a _ _ hb)
  intro z hz
  apply integral_congr_ae
  exact .of_forall fun σ=>cavityGeneratedSingleOriginOriginalFreshTaggedTest_event W c γ i A z hz σ

theorem cavityGeneratedTaggedOriginalFreshIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (i : ObservationLeaf (W.tree c))
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base) :
    (∫H,cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ (cavityGeneratedTaggedTestValue W A) i H
      ∂cavityGeneratedOriginalFreshChartMeasure μ a W c M γ) =
    ∫H,cavityGeneratedTaggedTerminalExpectation D μ a (cavityGeneratedSingleOriginChartForest W c γ .single)
      (cavityGeneratedSingleOriginOriginalFreshTaggedTest W c γ i A) H
      ∂cavityGeneratedOriginalFreshChartMeasure μ a W c M γ := by
  apply integral_congr_ae
  exact Measure.ae_smul_measure (singleOriginalFresh_ae D μ a W c M γ i A hA) 2

theorem cavityGeneratedTaggedCurrentIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c))
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base) :
    (∫H,cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ (cavityGeneratedTaggedTestValue W A) H
      ∂cavityGeneratedCurrentChartMeasure μ a W c M γ) =
    ∫H,cavityGeneratedTaggedTerminalExpectation D μ a (cavityGeneratedSingleOriginChartForest W c γ .current)
      (cavityGeneratedSingleOriginCurrentTaggedTest W c γ A) H
      ∂cavityGeneratedCurrentChartMeasure μ a W c M γ := by
  have hb : Measurable (cavityGeneratedSingleOriginCurrentTaggedTest W c γ A).base :=
    measurable_projectedBase A.base hA cavityGeneratedHistoryPrefix
      cavityGeneratedHistoryPrefix_measurable (cavityGeneratedSingleOriginOldTerminal W c γ .current)
  have he : ∀ᵐH ∂cavityGeneratedSingleOriginChartMeasure μ a W c M γ,
      cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ (cavityGeneratedTaggedTestValue W A) H =
      cavityGeneratedTaggedTerminalExpectation D μ a (cavityGeneratedSingleOriginChartForest W c γ .current)
        (cavityGeneratedSingleOriginCurrentTaggedTest W c γ A) H := by
    unfold cavityGeneratedSingleOriginChartMeasure
    apply expectation_ae_map _ _ (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ)
      _ (cavityGeneratedSingleOriginChart_append_measurable W c) _ _
      (measurable_cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ _
        (measurable_cavityGeneratedTaggedTestValue W A hA))
      (measurable_cavityGeneratedTaggedTerminalExpectation D μ a _ _ hb)
    intro z hz
    apply integral_congr_ae
    exact .of_forall fun σ=>cavityGeneratedSingleOriginCurrentTaggedTest_event W c γ A z hz σ
  exact integral_congr_ae (he.filter_mono (ae_mono (cavityGeneratedCurrentChartMeasure_le μ a W c M γ)))

private theorem crossTaggedTest_event
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ δ : PrintedGeneratedOriginChart (W.component c)) (χ : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedTaggedTest n W d) (z : CavityGeneratedCrossOriginPayload W c)
    (hz : z∈cavityGeneratedCrossOriginChartEvent W c γ δ χ)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedCrossOriginChartForest W c γ δ χ).depth
      (cavityGeneratedCrossOriginChartForest W c γ δ χ).tree) :
    cavityGeneratedCrossOriginTest W c γ δ χ (cavityGeneratedTaggedTestValue W A)
      (cavityGeneratedCrossOriginAppend W c z) σ =
    cavityGeneratedTaggedTestValue (cavityGeneratedCrossOriginChartForest W c γ δ χ)
      (cavityGeneratedCrossOriginTaggedTest W c γ δ χ A) (cavityGeneratedCrossOriginAppend W c z,σ) := by
  rw [cavityGeneratedCrossOriginChartEvent_eq] at hz
  have ht₁ : cavityGeneratedOriginSelectionClock W c z.1 =
      printedGeneratedOriginChartClock (W.component c) γ z.1.1
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2) := by
    rw [cavityGeneratedOriginSelectionClock_eq_chart,hz.1.1]
  have ht₂ : cavityGeneratedOriginSecondSelectionClock W c z =
      printedGeneratedOriginChartClock (W.component c) δ z.1.1
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    change cavityGeneratedOriginSelectionClock W c (z.1.1,z.2)=_
    rw [cavityGeneratedOriginSelectionClock_eq_chart,hz.2.1.1]
  have hk : printedGeneratedOriginCrossChartHolds (W.component c) γ δ χ
      (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2)
      (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    rcases γ with i | (i | u) <;> rcases δ with j | (j | v)
    all_goals try trivial
    exact hz.2.2
  unfold cavityGeneratedCrossOriginAppend
  rw [ht₁,ht₂]
  exact cavityGeneratedCrossOriginTaggedTest_receiver W c γ δ χ A z.1.1
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2)
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2)
    hz.1.2.1 hz.1.2.2 hz.2.1.2.2 hk σ

theorem cavityGeneratedTaggedCrossIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ δ : PrintedGeneratedOriginChart (W.component c)) (χ : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base) :
    (∫H,cavityGeneratedCrossOriginExpectation D μ a W c γ δ χ (cavityGeneratedTaggedTestValue W A) H
      ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ δ χ) =
    ∫H,cavityGeneratedTaggedTerminalExpectation D μ a (cavityGeneratedCrossOriginChartForest W c γ δ χ)
      (cavityGeneratedCrossOriginTaggedTest W c γ δ χ A) H
      ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ δ χ := by
  have hb : Measurable (cavityGeneratedCrossOriginTaggedTest W c γ δ χ A).base :=
    measurable_projectedBase A.base hA
      (fun H=>cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H))
      (cavityGeneratedHistoryPrefix_measurable.comp cavityGeneratedHistoryPrefix_measurable)
      (cavityGeneratedCrossOriginOldTerminal W c γ δ χ)
  apply integral_congr_ae
  unfold cavityGeneratedCrossOriginChartMeasure
  apply expectation_ae_map _ _ (measurableSet_cavityGeneratedCrossOriginChartEvent W c γ δ χ)
    _ (measurable_cavityGeneratedCrossOriginAppend W c) _ _
    (measurable_cavityGeneratedCrossOriginExpectation D μ a W c γ δ χ _
      (measurable_cavityGeneratedTaggedTestValue W A hA))
    (measurable_cavityGeneratedTaggedTerminalExpectation D μ a _ _ hb)
  intro z hz
  apply integral_congr_ae
  exact .of_forall fun σ=>crossTaggedTest_event W c γ δ χ A z hz σ

theorem cavityGeneratedTaggedFutureIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base) :
    (∫H,cavityGeneratedFutureOriginExpectation D μ a W c γ j (cavityGeneratedTaggedTestValue W A) H
      ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j) =
    ∫H,cavityGeneratedTaggedTerminalExpectation D μ a (cavityGeneratedFutureOriginChartForest W c γ j)
      (cavityGeneratedFutureOriginTaggedTest W c γ j A) H
      ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j := by
  have hb : Measurable (cavityGeneratedFutureOriginTaggedTest W c γ j A).base :=
    measurable_projectedBase A.base hA
      (fun H=>cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H))
      (cavityGeneratedHistoryPrefix_measurable.comp cavityGeneratedHistoryPrefix_measurable)
      (cavityGeneratedFutureOriginOldTerminal W c γ j)
  apply integral_congr_ae
  unfold cavityGeneratedFutureOriginChartSourceMeasure
  apply expectation_ae_map _ _ (measurableSet_cavityGeneratedFutureOriginChartSourceEvent W c γ j)
    _ (measurable_cavityGeneratedFutureOriginChartAppend W c) _ _
    (measurable_cavityGeneratedFutureOriginExpectation D μ a W c γ j _
      (measurable_cavityGeneratedTaggedTestValue W A hA))
    (measurable_cavityGeneratedTaggedTerminalExpectation D μ a _ _ hb)
  intro z hz
  apply integral_congr_ae
  exact .of_forall fun σ=>cavityGeneratedFutureOriginTaggedTest_source W c γ j A z hz σ

end QuantitativeFollowup
