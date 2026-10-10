module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTaggedComputedStepSourceCoverageDefinitions

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

theorem measurable_cavityGeneratedObservedRawTaggedTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (hA : Measurable A.base) :
    Measurable (cavityGeneratedObservedRawTaggedTerminalExpectation D μ a W A) :=
  ((measurable_cavityGeneratedObservedRawTaggedValue W A hA).stronglyMeasurable.integral_kernel_prod_right'
    (κ := cavityGeneratedRawForestTerminalKernel D μ a W.depth W.tree W.clock W.measurable_clock W.clock_antitone)).measurable

private theorem expectation_ae_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Measure X) (S : Set X) (hS : MeasurableSet S)
    (π : X → Y) (hπ : Measurable π) (f g : Y → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀x∈S,f (π x)=g (π x)) :
    ∀ᵐy ∂(M.restrict S).map π,f y=g y := by
  apply (ae_map_iff hπ.aemeasurable (measurableSet_eq_fun hf hg)).mpr
  exact (ae_restrict_mem hS).mono (fun x hx=>he x hx)

theorem cavityGeneratedObservedRawTaggedOriginalExpectation
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c)) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k (cavityGeneratedObservedRawTaggedValue W A) h =
      cavityGeneratedObservedRawTaggedTerminalExpectation D μ a W (cavityGeneratedObservedRawOriginalTaggedTest W c i k A) h := by
  apply integral_congr_ae
  exact .of_forall fun σ=>cavityGeneratedObservedRawOriginalTaggedTest_receiver hn W c i k A h σ

theorem cavityGeneratedObservedRawTaggedNormalizerExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W
      (fun h σ=>cavityGeneratedObservedRawTaggedValue W A (h,σ)) H =
      cavityGeneratedObservedRawTaggedTerminalExpectation D μ a (cavityGeneratedObservedRawNormalizerForest W)
        (cavityGeneratedObservedRawNormalizerTaggedSuccessor W A) H := by
  apply integral_congr_ae
  exact .of_forall fun σ=>(cavityGeneratedObservedRawNormalizerTaggedSuccessor_value W A H σ).symm

private theorem singleOriginalFresh_ae
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (i : ObservationLeaf (W.tree c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    ∀ᵐH ∂cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ,
      cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ (cavityGeneratedObservedRawTaggedValue W A) i H =
      cavityGeneratedObservedRawTaggedTerminalExpectation D μ a (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
        (cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A) H := by
  have hb := cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest_base_measurable W c γ i A hA
  unfold cavityGeneratedObservedRawSingleOriginChartMeasure cavityGeneratedRawOriginSourceMeasure
  apply expectation_ae_map _ _ (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ)
    _ (measurable_cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) _ _
    (measurable_cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ _
      (measurable_cavityGeneratedObservedRawTaggedValue W A hA) i)
    (measurable_cavityGeneratedObservedRawTaggedTerminalExpectation D μ a _ _ hb)
  intro z hz
  apply integral_congr_ae
  exact .of_forall fun σ=>cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest_event W c γ i A z hz σ

theorem cavityGeneratedObservedRawTaggedOriginalFreshIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (i : ObservationLeaf (W.tree c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    (∫H,cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ (cavityGeneratedObservedRawTaggedValue W A) i H
      ∂cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ) =
    ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
      (cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A) H
      ∂cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ := by
  apply integral_congr_ae
  exact Measure.ae_smul_measure (singleOriginalFresh_ae D μ a W c M γ i A hA) 2

theorem cavityGeneratedObservedRawTaggedCurrentIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    (∫H,cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ (cavityGeneratedObservedRawTaggedValue W A) H
      ∂cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ) =
    ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
      (cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A) H
      ∂cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ := by
  have hb := cavityGeneratedObservedRawSingleOriginCurrentTaggedTest_base_measurable W c γ A hA
  have he : ∀ᵐH ∂cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ,
      cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ (cavityGeneratedObservedRawTaggedValue W A) H =
      cavityGeneratedObservedRawTaggedTerminalExpectation D μ a (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
        (cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A) H := by
    unfold cavityGeneratedObservedRawSingleOriginChartMeasure cavityGeneratedRawOriginSourceMeasure
    apply expectation_ae_map _ _ (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ)
      _ (measurable_cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) _ _
      (measurable_cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ _
        (measurable_cavityGeneratedObservedRawTaggedValue W A hA))
      (measurable_cavityGeneratedObservedRawTaggedTerminalExpectation D μ a _ _ hb)
    intro z hz
    apply integral_congr_ae
    exact .of_forall fun σ=>cavityGeneratedObservedRawSingleOriginCurrentTaggedTest_event W c γ A z hz σ
  exact integral_congr_ae (he.filter_mono (ae_mono (cavityGeneratedObservedRawCurrentChartMeasure_le μ a W c M γ)))

private theorem selectedCell_chartClock
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection (W.tree c))
    (hg : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
      (cavityGeneratedObservedRawCrossFreeClock (W.tree c) g)) :
    cavityGeneratedRawCrossCell (W.clock h c) (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
      (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) (h,g)) := by
  rcases g with i | (z | u)
  · trivial
  · exact hg
  · trivial

private theorem crossTaggedTest_event
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (χ : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedObservedRawTaggedTest n W d) (z : CavityGeneratedObservedRawCrossPayload W c)
    (hz : z∈cavityGeneratedObservedRawCrossChartEvent W c γ δ χ)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ χ).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ χ).tree) :
    cavityGeneratedObservedRawCrossTest W c γ δ χ (cavityGeneratedObservedRawTaggedValue W A)
      (cavityGeneratedRawOriginDoubleAppendedHistory (fun h=>W.clock h c) (W.tree c) z) σ =
    cavityGeneratedObservedRawTaggedValue (cavityGeneratedObservedRawCrossChartForest W c γ δ χ)
      (cavityGeneratedObservedRawCrossTaggedTest W c γ δ χ A)
      (cavityGeneratedRawOriginDoubleAppendedHistory (fun h=>W.clock h c) (W.tree c) z,σ) := by
  rcases z with ⟨⟨h,g⟩,g'⟩
  rcases (cavityGeneratedObservedRawCrossChartEvent_iff W c γ δ χ ((h,g),g')).mp hz with
    ⟨⟨hγ,_,hr⟩,⟨hδ,_,hl⟩,hk⟩
  subst γ
  subst δ
  exact cavityGeneratedObservedRawCrossTaggedTest_receiver W c _ _ χ A h _ _
    (selectedCell_chartClock W c h g hr) (selectedCell_chartClock W c h g' hl) σ

theorem cavityGeneratedObservedRawTaggedCrossIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (χ : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    (∫H,cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ χ (cavityGeneratedObservedRawTaggedValue W A) H
      ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ χ M) =
    ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a (cavityGeneratedObservedRawCrossChartForest W c γ δ χ)
      (cavityGeneratedObservedRawCrossTaggedTest W c γ δ χ A) H
      ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ χ M := by
  have hb := measurable_cavityGeneratedObservedRawCrossTaggedTest_base W c γ δ χ A hA
  apply integral_congr_ae
  unfold cavityGeneratedObservedRawCrossChartMeasure cavityGeneratedRawOriginCrossSourceMeasure
  apply expectation_ae_map _ _ (measurableSet_cavityGeneratedObservedRawCrossChartEvent W c γ δ χ)
    _ (measurable_cavityGeneratedRawOriginDoubleAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) _ _
    (measurable_cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ χ _
      (measurable_cavityGeneratedObservedRawTaggedValue W A hA))
    (measurable_cavityGeneratedObservedRawTaggedTerminalExpectation D μ a _ _ hb)
  intro z hz
  apply integral_congr_ae
  exact .of_forall fun σ=>crossTaggedTest_event W c γ δ χ A z hz σ

theorem cavityGeneratedObservedRawTaggedFutureIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    (∫H,cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j (cavityGeneratedObservedRawTaggedValue W A) H
      ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) =
    ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a (cavityGeneratedObservedRawFutureForest W c γ j)
      (cavityGeneratedObservedRawFutureTaggedTest W c γ j A) H
      ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M := by
  have hb := measurable_cavityGeneratedObservedRawFutureTaggedTest_base W c γ j A hA
  apply integral_congr_ae
  unfold cavityGeneratedObservedRawFutureSourceMeasure cavityGeneratedRawOriginFutureSourceMeasure
  apply expectation_ae_map _ _ (measurableSet_cavityGeneratedObservedRawFutureSourceEvent W c γ j)
    _ (measurable_cavityGeneratedObservedRawFutureAppend W c) _ _
    (measurable_cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j _
      (measurable_cavityGeneratedObservedRawTaggedValue W A hA))
    (measurable_cavityGeneratedObservedRawTaggedTerminalExpectation D μ a _ _ hb)
  intro z hz
  apply integral_congr_ae
  exact .of_forall fun σ=>cavityGeneratedObservedRawFutureTaggedTest_source W c γ j A z hz σ

end QuantitativeFollowup
