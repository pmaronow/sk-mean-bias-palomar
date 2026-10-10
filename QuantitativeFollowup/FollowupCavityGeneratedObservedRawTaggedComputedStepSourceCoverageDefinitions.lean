module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageMain
public import QuantitativeFollowup.SupportingGeneratedObservedRawTaggedBounds
public import QuantitativeFollowup.SupportingGeneratedObservedRawOriginalTaggedTest
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginTaggedTests
public import QuantitativeFollowup.SupportingGeneratedObservedRawCrossPairTransport
public import QuantitativeFollowup.SupportingGeneratedObservedRawFuturePairTransport
public import QuantitativeFollowup.SupportingGeneratedObservedRawNormalizerPairTransport

@[expose] public section

/-! Literal tagged successor integrals use the same six computed families
and the same source measures as the actual whole-forest streaming step.
Every terminal test retains all preceding physical pair tags. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m d : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedObservedRawTaggedTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  ∫σ,cavityGeneratedObservedRawTaggedValue W A (h,σ)
    ∂cavityGeneratedRawForestTerminalKernel D μ a W.depth W.tree W.clock W.measurable_clock W.clock_antitone h

def cavityGeneratedObservedRawTaggedStreamingComponentSuccessorIntegralSum
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A : CavityGeneratedObservedRawTaggedTest n W d) : ℝ :=
    (∑i : ObservationLeaf (W.tree c),∑k : ObservationLeaf (W.tree c),
      ∫h,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a W
        (cavityGeneratedObservedRawOriginalTaggedTest W c i k A) h ∂M) -
    (∑i : ObservationLeaf (W.tree c),∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
      ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .single)
        (cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest W c γ i A) H
        ∂cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ) +
    (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
      ∑δ : CavityGeneratedObservedRawOriginChart (W.tree c),∑χ : NativeStreamingGeneratedCrossEdgeChart,
      ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a
        (cavityGeneratedObservedRawCrossChartForest W c γ δ χ)
        (cavityGeneratedObservedRawCrossTaggedTest W c γ δ χ A) H
        ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ χ M) +
    (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
      ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a
        (cavityGeneratedObservedRawSingleOriginChartForest W c γ .current)
        (cavityGeneratedObservedRawSingleOriginCurrentTaggedTest W c γ A) H
        ∂cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ) +
    (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),∑j : Fin (W.depth c),
      ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a
        (cavityGeneratedObservedRawFutureForest W c γ j)
        (cavityGeneratedObservedRawFutureTaggedTest W c γ j A) H
        ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) +
    ∫H,cavityGeneratedObservedRawTaggedTerminalExpectation D μ a
      (cavityGeneratedObservedRawNormalizerForest W)
      (cavityGeneratedObservedRawNormalizerTaggedSuccessor W A) H
      ∂cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M

def cavityGeneratedObservedRawTaggedStreamingStepSuccessorIntegralSum
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A : CavityGeneratedObservedRawTaggedTest n W d) : ℝ :=
  ∑c : Fin W.componentCount,
    cavityGeneratedObservedRawTaggedStreamingComponentSuccessorIntegralSum D μ a W c M A

end QuantitativeFollowup
