module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawStreamingStepSourceCoverage
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginSourceReceiverMeasurable
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossSourceReceiver
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageFutureExpectation
public import QuantitativeFollowup.SupportingGeneratedObservedRawNormalizerSourceReceiver

@[expose] public section

/-! One raw source step has exactly six computed successor families.
Their observables use the full old joint terminal test. The measures
retain both original cross selections, the current CDF weight, the
strict halfclosed future draw, and the independent normalizer component.
The physical coupling remains outside this sum. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

def cavityGeneratedObservedRawStreamingComponentSuccessorIntegralSum
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) : ℝ :=
  (∑i : ObservationLeaf (W.tree c), ∑k : ObservationLeaf (W.tree c),
    ∫h, cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F h ∂M) -
  (∑i : ObservationLeaf (W.tree c), ∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
    ∫H, cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F i H
      ∂cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ) +
  (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
    ∑δ : CavityGeneratedObservedRawOriginChart (W.tree c), ∑χ : NativeStreamingGeneratedCrossEdgeChart,
    ∫H, cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ χ F H
      ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ χ M) +
  (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
    ∫H, cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F H
      ∂cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ) +
  (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c), ∑j : Fin (W.depth c),
    ∫H, cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F H
      ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) +
  ∫H, cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W (fun h σ => F (h,σ)) H
    ∂cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M

def cavityGeneratedObservedRawStreamingStepSuccessorIntegralSum
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) : ℝ :=
  ∑c : Fin W.componentCount,
    cavityGeneratedObservedRawStreamingComponentSuccessorIntegralSum D μ a W c M F

end QuantitativeFollowup
