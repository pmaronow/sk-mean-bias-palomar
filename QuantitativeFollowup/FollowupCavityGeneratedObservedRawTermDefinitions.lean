module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossChartCoverage
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawNormalizerFamily
public import QuantitativeFollowup.SupportingGeneratedStreamingCountConstants

@[expose] public section

/-! Actual observed streaming paths retain arbitrary unary clock levels.
Their measures contain absolute internal source coefficients, while the
physical factor alpha/2 is exterior. Every successor is computed by its
original-origin source factory; support, sizes and budgets are derived
later from these constructors. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
variable {C : ℕ}

inductive CavityGeneratedActualObservedRawStreamingTerm
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C) :
    (r m : ℕ) → CavityGeneratedObservedRawForest m →
      Measure (CavityGeneratedHistory Paper.Overlap m) → Prop
  | initial : CavityGeneratedActualObservedRawStreamingTerm μ a S 0 1
      (cavityGeneratedObservedRawInitialForest S)
      (printedGeneratedInitialHistoryMeasure (parisiFreeMeasure μ a))
  | original {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) (b e : ObservationLeaf (W.tree c)) :
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) m W M
  | originalFresh {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) (b : ObservationLeaf (W.tree c))
      (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+1)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
        (cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ)
  | cross {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount)
      (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
      (χ : NativeStreamingGeneratedCrossEdgeChart) :
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+2)
        (cavityGeneratedObservedRawCrossChartForest W c γ δ χ)
        (cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ χ M)
  | current {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+1)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
        (cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ)
  | future {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
      (j : Fin (W.depth c)) :
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+2)
        (cavityGeneratedObservedRawFutureForest W c γ j)
        (cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M)
  | normalizer {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) :
      CavityGeneratedActualObservedRawStreamingTerm μ a S (r+1) (m+1)
        (cavityGeneratedObservedRawNormalizerForest W)
        (cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M)

end QuantitativeFollowup
