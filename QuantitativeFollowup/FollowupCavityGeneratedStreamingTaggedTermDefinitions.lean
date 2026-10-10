module
public import QuantitativeFollowup.SupportingGeneratedOriginalPairTransport
public import QuantitativeFollowup.SupportingGeneratedSingleOriginTaggedTests
public import QuantitativeFollowup.SupportingGeneratedCrossOriginPairTransport
public import QuantitativeFollowup.SupportingGeneratedFutureOriginPairTransport
public import QuantitativeFollowup.SupportingGeneratedNormalizerPairTransport

@[expose] public section

/-! Actual recursively transformed source observables. Each constructor
uses the genuine computed mark measure, forest and tagged successor test.
Old physical pairs are transported and one actual new pair is appended. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
variable {n C : ℕ}

def cavityGeneratedInitialTaggedTest (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ) :
    CavityGeneratedTaggedTest n (cavityGeneratedInitialSiblingForest S) 0 where
  base := F
  pairs := Fin.elim0

inductive CavityGeneratedActualTaggedStreamingTerm
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ) :
    (r m : ℕ) → (W : CavityGeneratedConstructedForest m) →
      Measure (CavityGeneratedHistory Paper.Overlap m) → CavityGeneratedTaggedTest n W r → Prop
  | initial : CavityGeneratedActualTaggedStreamingTerm μ a S F 0 1
      (cavityGeneratedInitialSiblingForest S)
      (printedGeneratedInitialHistoryMeasure (parisiFreeMeasure μ a))
      (cavityGeneratedInitialTaggedTest S F)
  | original {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedTaggedTest n W r}
      (previous : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c)) :
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) m W M
        (cavityGeneratedOriginalTaggedTest W c i k A)
  | originalFresh {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedTaggedTest n W r}
      (previous : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (i : ObservationLeaf (W.tree c))
      (γ : PrintedGeneratedOriginChart (W.component c)) :
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedSingleOriginChartForest W c γ .single)
        (cavityGeneratedOriginalFreshChartMeasure μ a W c M γ)
        (cavityGeneratedSingleOriginOriginalFreshTaggedTest W c γ i A)
  | cross {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedTaggedTest n W r}
      (previous : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (γ δ : PrintedGeneratedOriginChart (W.component c))
      (χ : NativeStreamingGeneratedCrossEdgeChart) :
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+2)
        (cavityGeneratedCrossOriginChartForest W c γ δ χ)
        (cavityGeneratedCrossOriginChartMeasure μ a W c M γ δ χ)
        (cavityGeneratedCrossOriginTaggedTest W c γ δ χ A)
  | current {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedTaggedTest n W r}
      (previous : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c)) :
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+1)
        (cavityGeneratedSingleOriginChartForest W c γ .current)
        (cavityGeneratedCurrentChartMeasure μ a W c M γ)
        (cavityGeneratedSingleOriginCurrentTaggedTest W c γ A)
  | future {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedTaggedTest n W r}
      (previous : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
      (j : Fin (W.depth c)) :
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+2)
        (cavityGeneratedFutureOriginChartForest W c γ j)
        (cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j)
        (cavityGeneratedFutureOriginTaggedTest W c γ j A)
  | normalizer {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)} {A : CavityGeneratedTaggedTest n W r}
      (previous : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
      (c : Fin W.componentCount) :
      CavityGeneratedActualTaggedStreamingTerm μ a S F (r+1) (m+1)
        (printedGeneratedNormalizerAppendedForest W)
        (cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M)
        (printedGeneratedNormalizerTaggedSuccessor W A)

end QuantitativeFollowup
