module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTermThreeDefects
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageMain

@[expose] public section

/-! A genuine repeated raw source path has its actual next derivative
and its literal any-three bound on the same native forest and history law.
All sizes, support and mark budgets come from the computed six constructors;
arbitrary unary observations and complete joint terminal tests are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {n C r m : ℕ}

theorem cavityGeneratedActualObservedRawStreamingTerm_source_coverage
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : CavityGeneratedObservedRawInitialForest C)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L) :
    Integrable (fun h=>∑c : Fin W.componentCount,
      ∫σ,nativeStreamingSourceSixBracket D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) :
          Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) M ∧
    cavityGeneratedObservedRawStreamingStepSuccessorIntegralSum D μ a W M F =
      cavityGeneratedObservedRawStreamingStepRawSourceIntegral D μ a W M F := by
  have hb := cavityGeneratedActualObservedRawStreamingTerm_budget μ a ha hμ S H
  haveI : IsFiniteMeasure M := ⟨hb.1.trans_lt (ENNReal.natCast_lt_top _)⟩
  exact cavityGeneratedObservedRawStreamingStep_source_coverage D μ a ha hμ W M
    (cavityGeneratedActualObservedRawStreamingTerm_support μ a ha S H) F hF L hL hbound

theorem hasDerivWithinAt_cavityGeneratedActualObservedRawStreamingTerm_source_step
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : CavityGeneratedObservedRawInitialForest C)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (followupCavityGeneratedObservedRawForestHistoryExpectation β ρ hβ hρ μ a W M F)
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedObservedRawStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M F)
      (Icc (0:ℝ) 1) u := by
  have hb := cavityGeneratedActualObservedRawStreamingTerm_budget μ a ha hμ S H
  haveI : IsFiniteMeasure M := ⟨hb.1.trans_lt (ENNReal.natCast_lt_top _)⟩
  exact hasDerivWithinAt_cavityGeneratedObservedRawStreamingStep_successors
    hn β ρ hβ hρ μ a ha hμ W M
    (cavityGeneratedActualObservedRawStreamingTerm_support μ a ha S H) F hF L hL hbound u hu

theorem cavityGeneratedActualObservedRawStreamingTerm_computed_successors
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M) :
    (∀(c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c)),
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) m W M) ∧
    (∀(c : Fin W.componentCount) (i : ObservationLeaf (W.tree c))
      (γ : CavityGeneratedObservedRawOriginChart (W.tree c)),
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+1)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
        (cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ)) ∧
    (∀(c : Fin W.componentCount) (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
      (χ : NativeStreamingGeneratedCrossEdgeChart),
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+2)
        (cavityGeneratedObservedRawCrossChartForest W c γ δ χ)
        (cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ χ M)) ∧
    (∀(c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c)),
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+1)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
        (cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ)) ∧
    (∀(c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
      (j : Fin (W.depth c)),
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+2)
        (cavityGeneratedObservedRawFutureForest W c γ j)
        (cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M)) ∧
    (∀c : Fin W.componentCount,
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+1)
        (cavityGeneratedObservedRawNormalizerForest W)
        (cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M)) := by
  exact ⟨fun c i k=>.original H c i k,
    fun c i γ=>.originalFresh H c i γ,
    fun c γ δ χ=>.cross H c γ δ χ,
    fun c γ=>.current H c γ,
    fun c γ j=>.future H c γ j,
    fun c=>.normalizer H c⟩

theorem cavityGeneratedActualObservedRawStreamingTerm_source_step_three_defects
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : CavityGeneratedObservedRawInitialForest C)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (c : Fin 3→Fin W.componentCount)
    (b e : (j : Fin 3)→ObservationLeaf (W.tree (c j))) :
    HasDerivWithinAt
      (followupCavityGeneratedObservedRawForestHistoryExpectation β ρ hβ hρ μ a W M F)
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedObservedRawStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M F)
      (Icc (0:ℝ) 1) u ∧
    (∫h,cavityGeneratedForestThreeDefectMoment
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W.depth W.tree (W.clock h) c b e
      ∂(ENNReal.ofReal (|followupCavityAlpha n β ρ/2|^r) • M)) ≤
      |followupCavityAlpha n β ρ/2|^r *
        (printedGeneratedStreamingCubicConstant (cavityGeneratedObservedRawStreamingInitialLeafCount S) r : ℝ)*
          cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a := by
  exact ⟨hasDerivWithinAt_cavityGeneratedActualObservedRawStreamingTerm_source_step
      hn β ρ hβ hρ μ a ha hμ S H F hF L hL hbound u hu,
    cavityGeneratedActualObservedRawStreamingTerm_physical_three_defects
      hn β ρ hβ hρ μ a ha hμ S H u hu c b e⟩

end QuantitativeFollowup
