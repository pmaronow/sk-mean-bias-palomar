module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTermDefinitions
public import QuantitativeFollowup.SupportingGeneratedObservedRawOriginalTaggedTest
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginTaggedTests
public import QuantitativeFollowup.SupportingGeneratedObservedRawCrossPairTransport
public import QuantitativeFollowup.SupportingGeneratedObservedRawFuturePairTransport
public import QuantitativeFollowup.SupportingGeneratedObservedRawNormalizerPairTransport

@[expose] public section

/-! Repeated raw source observables use the actual six successor tests.
Each operation preserves every prior physical pair and appends its own
actual new pair, while retaining the original joint bounded base test. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
variable {n C : ℕ}

inductive CavityGeneratedActualObservedRawTaggedStreamingTerm
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ) :
    (r m : ℕ) → (W : CavityGeneratedObservedRawForest m) →
      Measure (CavityGeneratedHistory Paper.Overlap m) → CavityGeneratedObservedRawTaggedTest n W r → Prop
  | initial : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F 0 1
      (cavityGeneratedObservedRawInitialForest S)
      (printedGeneratedInitialHistoryMeasure (parisiFreeMeasure μ a))
      (cavityGeneratedObservedRawInitialTaggedTest S F)
  | original {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedObservedRawTaggedTest n W r}
      (previous : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c)) :
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) m W M
        (cavityGeneratedObservedRawOriginalTaggedTest W c i k A)
  | originalFresh {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedObservedRawTaggedTest n W r}
      (previous : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (i : ObservationLeaf (W.tree c))
      (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
        (cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ)
        (cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A)
  | cross {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedObservedRawTaggedTest n W r}
      (previous : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
      (χ : NativeStreamingGeneratedCrossEdgeChart) :
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+2)
        (cavityGeneratedObservedRawCrossChartForest W c γ δ χ)
        (cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ χ M)
        (cavityGeneratedObservedRawCrossTaggedTest W c γ δ χ A)
  | current {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedObservedRawTaggedTest n W r}
      (previous : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
        (cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ)
        (cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A)
  | future {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedObservedRawTaggedTest n W r}
      (previous : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
      (j : Fin (W.depth c)) :
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+2)
        (cavityGeneratedObservedRawFutureForest W c γ j)
        (cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M)
        (cavityGeneratedObservedRawFutureTaggedTest W c γ j A)
  | normalizer {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedObservedRawTaggedTest n W r}
      (previous : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) :
      CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedObservedRawNormalizerForest W)
        (cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M)
        (cavityGeneratedObservedRawNormalizerTaggedSuccessor W A)

end QuantitativeFollowup
