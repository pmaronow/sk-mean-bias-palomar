module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageStatic
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageSingle
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverSource
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverFubini
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiverPartition
public import QuantitativeFollowup.SupportingGeneratedNormalizerSourceReceiver

@[expose] public section

/-! The six computed successor families of one whole-forest source step.
All weights and chart measures are their genuine original-source weights.
The normalizer appends an independent binary component, once for each
selected original component. No physical coupling is absorbed here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

def cavityGeneratedStreamingComponentSuccessorIntegralSum
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) : ℝ :=
    (∑i : ObservationLeaf (W.tree c),∑k : ObservationLeaf (W.tree c),
      ∫h,cavityGeneratedStreamingOriginalExpectation D μ a W c i k F h ∂M) -
    (∑i : ObservationLeaf (W.tree c),∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i H
        ∂cavityGeneratedOriginalFreshChartMeasure μ a W c M γ) +
    (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∑δ : PrintedGeneratedOriginChart (W.component c),∑χ : NativeStreamingGeneratedCrossEdgeChart,
      ∫H,cavityGeneratedCrossOriginExpectation D μ a W c γ δ χ F H
        ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ δ χ) +
    (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H
        ∂cavityGeneratedCurrentChartMeasure μ a W c M γ) +
    (∑γ : PrintedGeneratedOriginChart (W.component c),∑j : Fin (W.depth c),
      ∫H,cavityGeneratedFutureOriginExpectation D μ a W c γ j F H
        ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j) +
    ∫H,printedGeneratedNormalizerSourceExpectation D μ a W (fun h σ=>F (h,σ)) H
      ∂cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M

def cavityGeneratedStreamingStepSuccessorIntegralSum
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) : ℝ :=
  ∑c : Fin W.componentCount,
    cavityGeneratedStreamingComponentSuccessorIntegralSum D μ a W c M F

def cavityGeneratedStreamingStepRawSourceIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) : ℝ :=
  ∫h,∑c : Fin W.componentCount,
    ∫σ,nativeStreamingSourceSixBracket D μ a (W.clockTemplate.clock h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _) ∂M

end QuantitativeFollowup
