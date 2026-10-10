module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawSourceThreeDefects
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTaggedTerm
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTaggedComputedStepSourceCoverage

@[expose] public section

/-! A repeatedly computed tagged observable needs only its original measurable
joint test and envelope. The actual six-step path derives all later test,
support and budget facts. Its cubic bound selects arbitrary final leaf pairs,
including pairs already present initially and the zero-step case. -/
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

theorem cavityGeneratedActualObservedRawTaggedStreamingTerm_source_coverage
    (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A) :
    Integrable (fun h=>∑c : Fin W.componentCount,
      ∫σ,nativeStreamingSourceSixBracket D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree
          (fun τ=>cavityGeneratedObservedRawTaggedValue W A (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) :
          Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) M ∧
    cavityGeneratedObservedRawTaggedStreamingStepSuccessorIntegralSum D μ a W M A =
      cavityGeneratedObservedRawStreamingStepRawSourceIntegral D μ a W M
        (cavityGeneratedObservedRawTaggedValue W A) := by
  have hp := cavityGeneratedActualObservedRawTaggedStreamingTerm_path μ a S F H
  have hb := cavityGeneratedActualObservedRawStreamingTerm_budget μ a ha hμ S hp
  haveI : IsFiniteMeasure M := ⟨hb.1.trans_lt (ENNReal.natCast_lt_top _)⟩
  exact cavityGeneratedObservedRawTaggedStreamingStep_source_coverage
    hn D μ a ha hμ W M (cavityGeneratedActualObservedRawStreamingTerm_support μ a ha S hp) A
    (cavityGeneratedActualObservedRawTaggedStreamingTerm_base_measurable μ a S F hF H) L hL
    (cavityGeneratedActualObservedRawTaggedStreamingTerm_base_abs_le μ a S F L hbound H)

theorem hasDerivWithinAt_cavityGeneratedActualObservedRawTaggedStreamingTerm_source_step
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (followupCavityGeneratedObservedRawForestHistoryExpectation β ρ hβ hρ μ a W M
        (cavityGeneratedObservedRawTaggedValue W A))
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedObservedRawTaggedStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M A)
      (Icc (0:ℝ) 1) u := by
  have hp := cavityGeneratedActualObservedRawTaggedStreamingTerm_path μ a S F H
  have hb := cavityGeneratedActualObservedRawStreamingTerm_budget μ a ha hμ S hp
  haveI : IsFiniteMeasure M := ⟨hb.1.trans_lt (ENNReal.natCast_lt_top _)⟩
  exact hasDerivWithinAt_cavityGeneratedObservedRawTaggedStreamingStep_successors
    hn β ρ hβ hρ μ a ha hμ W M (cavityGeneratedActualObservedRawStreamingTerm_support μ a ha S hp) A
    (cavityGeneratedActualObservedRawTaggedStreamingTerm_base_measurable μ a S F hF H) L hL
    (cavityGeneratedActualObservedRawTaggedStreamingTerm_base_abs_le μ a S F L hbound H) u hu

theorem cavityGeneratedActualObservedRawTaggedStreamingTerm_computed_successors
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A) :
    (∀(c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c)),
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) m W M
        (cavityGeneratedObservedRawOriginalTaggedTest W c i k A)) ∧
    (∀(c : Fin W.componentCount) (i : ObservationLeaf (W.tree c))
      (γ : CavityGeneratedObservedRawOriginChart (W.tree c)),
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
        (cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ)
        (cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A)) ∧
    (∀(c : Fin W.componentCount) (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
      (χ : NativeStreamingGeneratedCrossEdgeChart),
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+2)
        (cavityGeneratedObservedRawCrossChartForest W c γ δ χ)
        (cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ χ M)
        (cavityGeneratedObservedRawCrossTaggedTest W c γ δ χ A)) ∧
    (∀(c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c)),
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
        (cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ)
        (cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A)) ∧
    (∀(c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
      (j : Fin (W.depth c)),
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+2)
        (cavityGeneratedObservedRawFutureForest W c γ j)
        (cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M)
        (cavityGeneratedObservedRawFutureTaggedTest W c γ j A)) ∧
    (∀c : Fin W.componentCount,
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedObservedRawNormalizerForest W)
        (cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M)
        (cavityGeneratedObservedRawNormalizerTaggedSuccessor W A)) := by
  exact ⟨fun c i k=>.original H c i k,
    fun c i γ=>.originalFresh H c i γ,
    fun c γ δ χ=>.cross H c γ δ χ,
    fun c γ=>.current H c γ,
    fun c γ j=>.future H c γ j,
    fun c=>.normalizer H c⟩

theorem cavityGeneratedActualObservedRawTaggedStreamingTerm_source_step_three_defects
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (c : Fin 3→Fin W.componentCount)
    (b e : (j : Fin 3)→ObservationLeaf (W.tree (c j))) :
    HasDerivWithinAt
      (followupCavityGeneratedObservedRawForestHistoryExpectation β ρ hβ hρ μ a W M
        (cavityGeneratedObservedRawTaggedValue W A))
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedObservedRawTaggedStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M A)
      (Icc (0:ℝ) 1) u ∧
    (∫h,cavityGeneratedForestThreeDefectMoment
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W.depth W.tree (W.clock h) c b e
      ∂(ENNReal.ofReal (|followupCavityAlpha n β ρ/2|^r) • M)) ≤
      |followupCavityAlpha n β ρ/2|^r *
        (printedGeneratedStreamingCubicConstant (cavityGeneratedObservedRawStreamingInitialLeafCount S) r : ℝ)*
          cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a := by
  exact ⟨hasDerivWithinAt_cavityGeneratedActualObservedRawTaggedStreamingTerm_source_step
      hn β ρ hβ hρ μ a ha hμ S F hF L hL hbound H u hu,
    cavityGeneratedActualObservedRawStreamingTerm_physical_three_defects
      hn β ρ hβ hρ μ a ha hμ S
      (cavityGeneratedActualObservedRawTaggedStreamingTerm_path μ a S F H) u hu c b e⟩

end QuantitativeFollowup
