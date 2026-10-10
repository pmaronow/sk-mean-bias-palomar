module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverage
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTestBounds
public import QuantitativeFollowup.SupportingGeneratedOriginalPairTransport
public import QuantitativeFollowup.SupportingGeneratedSingleOriginTaggedTests
public import QuantitativeFollowup.SupportingGeneratedCrossOriginPairTransport
public import QuantitativeFollowup.SupportingGeneratedFutureOriginPairTransport
public import QuantitativeFollowup.SupportingGeneratedNormalizerPairTransport

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

def cavityGeneratedTaggedTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (A : CavityGeneratedTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  ∫σ,cavityGeneratedTaggedTestValue W A (h,σ)
    ∂cavityGeneratedForestTerminalKernel D μ a W h

def cavityGeneratedTaggedStreamingComponentSuccessorIntegralSum
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A : CavityGeneratedTaggedTest n W d) : ℝ :=
    (∑i : ObservationLeaf (W.tree c),∑k : ObservationLeaf (W.tree c),
      ∫h,cavityGeneratedTaggedTerminalExpectation D μ a W
        (cavityGeneratedOriginalTaggedTest W c i k A) h ∂M) -
    (∑i : ObservationLeaf (W.tree c),∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedTaggedTerminalExpectation D μ a
        (cavityGeneratedSingleOriginChartForest W c γ .single)
        (cavityGeneratedSingleOriginOriginalFreshTaggedTest W c γ i A) H
        ∂cavityGeneratedOriginalFreshChartMeasure μ a W c M γ) +
    (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∑δ : PrintedGeneratedOriginChart (W.component c),∑χ : NativeStreamingGeneratedCrossEdgeChart,
      ∫H,cavityGeneratedTaggedTerminalExpectation D μ a
        (cavityGeneratedCrossOriginChartForest W c γ δ χ)
        (cavityGeneratedCrossOriginTaggedTest W c γ δ χ A) H
        ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ δ χ) +
    (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedTaggedTerminalExpectation D μ a
        (cavityGeneratedSingleOriginChartForest W c γ .current)
        (cavityGeneratedSingleOriginCurrentTaggedTest W c γ A) H
        ∂cavityGeneratedCurrentChartMeasure μ a W c M γ) +
    (∑γ : PrintedGeneratedOriginChart (W.component c),∑j : Fin (W.depth c),
      ∫H,cavityGeneratedTaggedTerminalExpectation D μ a
        (cavityGeneratedFutureOriginChartForest W c γ j)
        (cavityGeneratedFutureOriginTaggedTest W c γ j A) H
        ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j) +
    ∫H,cavityGeneratedTaggedTerminalExpectation D μ a
      (printedGeneratedNormalizerAppendedForest W)
      (printedGeneratedNormalizerTaggedSuccessor W A) H
      ∂cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M

def cavityGeneratedTaggedStreamingStepSuccessorIntegralSum
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A : CavityGeneratedTaggedTest n W d) : ℝ :=
  ∑c : Fin W.componentCount,
    cavityGeneratedTaggedStreamingComponentSuccessorIntegralSum D μ a W c M A

end QuantitativeFollowup
