module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedThreeDefects
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedStepSourceCoverage

@[expose] public section

/-! A recursively computed tagged term has its genuine next source step.
The original measurable joint observable supplies all test hypotheses;
the path supplies finiteness, order and count bounds. Every successor in
the actual six-source sum is the corresponding next tagged term. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n C r m : ℕ}

theorem cavityGeneratedActualTaggedStreamingTerm_source_coverage
    (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A) :
    Integrable (fun h=>∑c : Fin W.componentCount,
      ∫σ,nativeStreamingSourceSixBracket D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree
          (fun τ=>cavityGeneratedTaggedTestValue W A (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock h) : Measure _)) M ∧
    cavityGeneratedTaggedStreamingStepSuccessorIntegralSum D μ a W M A =
      cavityGeneratedStreamingStepRawSourceIntegral D μ a W M (cavityGeneratedTaggedTestValue W A) := by
  have hp := cavityGeneratedActualTaggedStreamingTerm_path μ a S F H
  have hb := cavityGeneratedActualStreamingTerm_budget μ a ha hμ S hp
  haveI : IsFiniteMeasure M := ⟨hb.1.trans_lt (ENNReal.natCast_lt_top _)⟩
  exact cavityGeneratedTaggedStreamingStep_source_coverage hn D μ a ha hμ W M
    (cavityGeneratedActualStreamingTerm_order μ a ha S hp) A
    (cavityGeneratedActualTaggedStreamingTerm_base_measurable μ a S F hF H) L hL
    (cavityGeneratedActualTaggedStreamingTerm_base_abs_le μ a S F L hbound H)

theorem hasDerivWithinAt_cavityGeneratedActualTaggedStreamingTerm_source_step
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (followupCavityGeneratedForestHistoryExpectation β ρ hβ hρ μ a W M
        (fun h σ=>cavityGeneratedTaggedTestValue W A (h,σ)))
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedTaggedStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M A)
      (Icc (0:ℝ) 1) u := by
  have hp := cavityGeneratedActualTaggedStreamingTerm_path μ a S F H
  have hb := cavityGeneratedActualStreamingTerm_budget μ a ha hμ S hp
  haveI : IsFiniteMeasure M := ⟨hb.1.trans_lt (ENNReal.natCast_lt_top _)⟩
  exact hasDerivWithinAt_cavityGeneratedTaggedStreamingStep_successors
    hn β ρ hβ hρ μ a ha hμ W M (cavityGeneratedActualStreamingTerm_order μ a ha S hp) A
    (cavityGeneratedActualTaggedStreamingTerm_base_measurable μ a S F hF H) L hL
    (cavityGeneratedActualTaggedStreamingTerm_base_abs_le μ a S F L hbound H) u hu

theorem cavityGeneratedActualTaggedStreamingTerm_computed_successors
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A) :
    (∀(c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c)),
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) m W M
        (cavityGeneratedOriginalTaggedTest W c i k A)) ∧
    (∀(c : Fin W.componentCount) (i : ObservationLeaf (W.tree c))
      (γ : PrintedGeneratedOriginChart (W.component c)),
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedSingleOriginChartForest W c γ .single)
        (cavityGeneratedOriginalFreshChartMeasure μ a W c M γ)
        (cavityGeneratedSingleOriginOriginalFreshTaggedTest W c γ i A)) ∧
    (∀(c : Fin W.componentCount) (γ δ : PrintedGeneratedOriginChart (W.component c))
      (χ : NativeStreamingGeneratedCrossEdgeChart),
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+2)
        (cavityGeneratedCrossOriginChartForest W c γ δ χ)
        (cavityGeneratedCrossOriginChartMeasure μ a W c M γ δ χ)
        (cavityGeneratedCrossOriginTaggedTest W c γ δ χ A)) ∧
    (∀(c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c)),
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedSingleOriginChartForest W c γ .current)
        (cavityGeneratedCurrentChartMeasure μ a W c M γ)
        (cavityGeneratedSingleOriginCurrentTaggedTest W c γ A)) ∧
    (∀(c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
      (j : Fin (W.depth c)),
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+2)
        (cavityGeneratedFutureOriginChartForest W c γ j)
        (cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j)
        (cavityGeneratedFutureOriginTaggedTest W c γ j A)) ∧
    (∀c : Fin W.componentCount,
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+1)
        (printedGeneratedNormalizerAppendedForest W)
        (cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M)
        (printedGeneratedNormalizerTaggedSuccessor W A)) := by
  exact ⟨fun c i k=>.original H c i k,
    fun c i γ=>.originalFresh H c i γ,
    fun c γ δ χ=>.cross H c γ δ χ,
    fun c γ=>.current H c γ,
    fun c γ j=>.future H c γ j,
    fun c=>.normalizer H c⟩

theorem cavityGeneratedActualTaggedStreamingTerm_source_step_three_defects
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (ι : Fin 3 → Fin r) :
    HasDerivWithinAt
      (followupCavityGeneratedForestHistoryExpectation β ρ hβ hρ μ a W M
        (fun h σ=>cavityGeneratedTaggedTestValue W A (h,σ)))
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedTaggedStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M A)
      (Icc (0:ℝ) 1) u ∧
    (∫h,cavityGeneratedTaggedThreeDefectMoment
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W A ι h
      ∂(ENNReal.ofReal (|followupCavityAlpha n β ρ/2|^r) • M)) ≤
      |followupCavityAlpha n β ρ/2|^r *
        (printedGeneratedStreamingCubicConstant (cavityGeneratedStreamingInitialLeafCount S) r : ℝ)*
          cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a := by
  exact ⟨hasDerivWithinAt_cavityGeneratedActualTaggedStreamingTerm_source_step
    hn β ρ hβ hρ μ a ha hμ S F hF L hL hbound H u hu,
    cavityGeneratedActualTaggedStreamingTerm_physical_three_defects
      hn β ρ hβ hρ μ a ha hμ S F H u hu ι⟩

end QuantitativeFollowup
