module
public import QuantitativeFollowup.SupportingGeneratedInitialSourceFamily
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginWeights
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedNormalizerFamily
public import QuantitativeFollowup.SupportingGeneratedStreamingCountConstants

@[expose] public section

/-! A normalized streaming term starts with the actual free mark and can
only be produced by one of the six concrete source operations. Every
output measure and forest is computed by its genuine receiver factory.
The physical factor alpha/2 is exterior to these mark measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
variable {C : ℕ}

inductive CavityGeneratedActualStreamingTerm
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape) :
    (r m : ℕ) → CavityGeneratedConstructedForest m →
      Measure (CavityGeneratedHistory Paper.Overlap m) → Prop
  | initial : CavityGeneratedActualStreamingTerm μ a S 0 1
      (cavityGeneratedInitialSiblingForest S)
      (printedGeneratedInitialHistoryMeasure (parisiFreeMeasure μ a))
  | original {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) (b e : ObservationLeaf (W.tree c)) :
      CavityGeneratedActualStreamingTerm μ a S (r+1) m W M
  | originalFresh {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) (b : ObservationLeaf (W.tree c))
      (γ : PrintedGeneratedOriginChart (W.component c)) :
      CavityGeneratedActualStreamingTerm μ a S (r+1) (m+1)
        (cavityGeneratedSingleOriginChartForest W c γ .single)
        (cavityGeneratedOriginalFreshChartMeasure μ a W c M γ)
  | cross {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount)
      (γ δ : PrintedGeneratedOriginChart (W.component c))
      (χ : NativeStreamingGeneratedCrossEdgeChart) :
      CavityGeneratedActualStreamingTerm μ a S (r+1) (m+2)
        (cavityGeneratedCrossOriginChartForest W c γ δ χ)
        (cavityGeneratedCrossOriginChartMeasure μ a W c M γ δ χ)
  | current {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c)) :
      CavityGeneratedActualStreamingTerm μ a S (r+1) (m+1)
        (cavityGeneratedSingleOriginChartForest W c γ .current)
        (cavityGeneratedCurrentChartMeasure μ a W c M γ)
  | future {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
      (j : Fin (W.depth c)) :
      CavityGeneratedActualStreamingTerm μ a S (r+1) (m+2)
        (cavityGeneratedFutureOriginChartForest W c γ j)
        (cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j)
  | normalizer {r m : ℕ} {W : CavityGeneratedConstructedForest m}
      {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
      (previous : CavityGeneratedActualStreamingTerm μ a S r m W M)
      (c : Fin W.componentCount) :
      CavityGeneratedActualStreamingTerm μ a S (r+1) (m+1)
        (printedGeneratedNormalizerAppendedForest W)
        (cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M)

end QuantitativeFollowup
