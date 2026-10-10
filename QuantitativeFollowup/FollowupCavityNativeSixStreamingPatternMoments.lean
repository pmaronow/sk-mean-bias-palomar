module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingAttachmentPattern
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalDefectTests
public import QuantitativeFollowup.FollowupCavityThirdMoment

@[expose] public section

/-! Every source pattern below evaluates a literal defect under its
actual complete marked law.  The final pattern is a product of genuine
independent expectations; none is defined from a derivative. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
attribute [local instance] Classical.propDecidable

def nativeStreamingOriginCommonClock (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) :
    NativeStreamingOrigin T → NativeStreamingOrigin T → Paper.Overlap
  | .vertex v, .vertex w => q (finiteCascadeCommonPathDepth T v w)
  | .edge e r, .vertex v => nativeStreamingOldSelectedCommonClock
      (finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)) e.depth r
        (q (finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)))
  | .vertex v, .edge e r => nativeStreamingOldSelectedCommonClock
      (finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)) e.depth r
        (q (finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)))
  | .edge e r, .edge f l => nativeStreamingSelectedCommonClock
      (finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e)
        (nativeStreamingEdgeChildVertex f)) e.depth f.depth r l
          (q (finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e)
            (nativeStreamingEdgeChildVertex f)))

def nativeStreamingOldTerminalExpectation (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  ∫z, F (finiteCascadeRecordTerminalSpins T z.2)
    ∂anisotropicRecordedProfileTreeLaw D μ a q T

def nativeStreamingPatternMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    NativeStreamingAttachmentPattern T → ℝ
  | .original i k => if i=k then 0 else
      ∫z, F (finiteCascadeRecordTerminalSpins T z.2) *
        cavitySpinOverlapDefect n (q (observationCommonLevel T i k))
          (observationLeafSpin T i z.2) (observationLeafSpin T k z.2)
        ∂anisotropicRecordedProfileTreeLaw D μ a q T
  | .originalFresh i o =>
      nativeStreamingTerminalMarkMoment (nativeStreamingOriginSingleProbability D μ a q T o)
        (nativeStreamingOriginalFreshSpinTest T F i
          (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) o))
  | .cross o p =>
      nativeStreamingTerminalMarkMoment (nativeStreamingOriginCrossProbability D μ a q T o p)
        (nativeStreamingDefectSpinTest T F (nativeStreamingOriginCommonClock q T o p))
  | .current o =>
      nativeStreamingTerminalMarkMoment (nativeStreamingOriginCurrentProbability D μ a q T o)
        (nativeStreamingDefectSpinTest T F (nativeStreamingOriginLevel q o))
  | .future o j l =>
      nativeStreamingTerminalMarkMoment (nativeStreamingOriginFutureProbability D μ a q T o j l)
        (nativeStreamingDefectSpinTest T F l)
  | .normalizer l => nativeStreamingOldTerminalExpectation D μ a q T F *
      (∫z, cavitySpinOverlapDefect n l z.2.1 z.2.2 ∂anisotropicFreshTerminalPairLaw D μ a l)

theorem nativeStreamingPatternMoment_original_diagonal
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (i : ObservationLeaf T) :
    nativeStreamingPatternMoment D μ a q T F (.original i i)=0 := by
  simp only [nativeStreamingPatternMoment, ite_true]

theorem nativeStreamingPatternMoment_normalizer_independent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (l : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.normalizer l)=
      nativeStreamingOldTerminalExpectation D μ a q T F *
        (∫z, cavitySpinOverlapDefect n l z.2.1 z.2.2 ∂anisotropicFreshTerminalPairLaw D μ a l) := rfl

end QuantitativeFollowup
