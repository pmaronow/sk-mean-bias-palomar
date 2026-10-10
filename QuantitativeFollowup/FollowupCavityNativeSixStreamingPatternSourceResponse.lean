module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternOriginalSourceDerivative
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternRefinedSourceDerivatives
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternNormalizerSourceDerivative

@[expose] public section

/-! The concrete source response of each marked integrand. This is a
second application of the genuine first streaming formula on the actual
representing tree; the normalizer retains two independent components. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeStreamingOriginValid (q : ℕ → Paper.Overlap)
    {j : ℕ} {T : FiniteTerminalGenealogy j} : NativeStreamingOrigin T → Prop
  | .vertex _ => True
  | .edge e r => q (e.depth+1)≤r ∧ r≤q e.depth

def nativeStreamingPatternValid (q : ℕ → Paper.Overlap)
    {j : ℕ} {T : FiniteTerminalGenealogy j} : NativeStreamingAttachmentPattern T → Prop
  | .original _ _ => True
  | .originalFresh _ o => nativeStreamingOriginValid q o
  | .current o => nativeStreamingOriginValid q o
  | .cross o p => nativeStreamingOriginValid q o ∧ nativeStreamingOriginValid q p
  | .future o j l => nativeStreamingOriginValid q o ∧ (q (j+1)≤l ∧ l≤q j)
  | .normalizer _ => True

def nativeStreamingPatternSourceResponse (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    NativeStreamingAttachmentPattern T → ℝ
  | .original i k =>
    nativeStreamingSourceSixBracket
            D μ a q T
            (nativeStreamingPatternOriginalTerminalTest q T F i k)
  | .originalFresh i (.vertex v) =>
    nativeStreamingSourceSixBracket
            D μ a q
            (finiteCascadeContinuationGraft observationLinearTree v)
            (nativeStreamingPatternVertexTerminalTest .single T v
              (nativeStreamingOriginalFreshSpinTest T F i
                (q (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v))))
  | .originalFresh i (.edge e r) =>
    nativeStreamingSourceSixBracket
            D μ a (nativeStreamingEdgeSchedule q e.depth r)
            (finiteCascadeContinuationGraft observationLinearTree
              (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e))
            (nativeStreamingPatternRefinedVertexTerminalTest .single (nativeStreamingEdgeSubdivision e.depth)
              T (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
              (nativeStreamingOriginalFreshSpinTest T F i
                (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) (.edge e r))))
  | .current (.vertex v) =>
    nativeStreamingSourceSixBracket
            D μ a q
            (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)
            (nativeStreamingPatternVertexTerminalTest .current T v
              (nativeStreamingDefectSpinTest T F (q v.depth)))
  | .current (.edge e r) =>
    nativeStreamingSourceSixBracket
            D μ a (nativeStreamingEdgeSchedule q e.depth r)
            (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree
              (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e))
            (nativeStreamingPatternRefinedVertexTerminalTest .current (nativeStreamingEdgeSubdivision e.depth)
              T (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
              (nativeStreamingDefectSpinTest T F r))
  | .cross (.vertex v) (.vertex w) =>
    nativeStreamingSourceSixBracket
            D μ a q
            (finiteCascadeCrossContinuationGraft observationLinearTree v w)
            (nativeStreamingPatternCrossTerminalTest T v w
              (nativeStreamingDefectSpinTest T F (q (finiteCascadeCommonPathDepth T v w))))
  | .cross (.edge e r) (.vertex v) =>
    nativeStreamingSourceSixBracket
            D μ a (nativeStreamingEdgeSchedule q e.depth r)
            (finiteCascadeCrossContinuationGraft observationLinearTree
              (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
              (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v))
            (nativeStreamingPatternRefinedCrossTerminalTest (nativeStreamingEdgeSubdivision e.depth) T
              (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
              (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v)
              (nativeStreamingDefectSpinTest T F
                (nativeStreamingOriginCommonClock q T (.edge e r) (.vertex v))))
  | .cross (.vertex v) (.edge e r) =>
    nativeStreamingSourceSixBracket
            D μ a (nativeStreamingEdgeSchedule q e.depth r)
            (finiteCascadeCrossContinuationGraft observationLinearTree
              (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
              (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v))
            (nativeStreamingPatternRefinedCrossTerminalTest (nativeStreamingEdgeSubdivision e.depth) T
              (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
              (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v)
              (nativeStreamingDefectSpinTest T F
                (nativeStreamingOriginCommonClock q T (.edge e r) (.vertex v))))
  | .cross (.edge e r) (.edge f l) =>
    nativeStreamingSourceSixBracket
            D μ a
            (nativeStreamingPairObservationSchedule q e.depth f.depth r l)
            (finiteCascadeCrossContinuationGraft observationLinearTree
              (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
                (nativeStreamingPairObservationIndex e.depth f.depth r l))
              (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f
                (nativeStreamingPairObservationIndex f.depth e.depth l r)))
            (nativeStreamingPatternRefinedCrossTerminalTest nativeStreamingPairObservationSubdivision T
              (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
                (nativeStreamingPairObservationIndex e.depth f.depth r l))
              (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f
                (nativeStreamingPairObservationIndex f.depth e.depth l r))
              (nativeStreamingDefectSpinTest T F
                (nativeStreamingOriginCommonClock q T (.edge e r) (.edge f l))))
  | .future (.vertex v) j l =>
    nativeStreamingSourceSixBracket
            D μ a (nativeStreamingEdgeSchedule q j l)
            (finiteCascadeFutureVertexGraft
              (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v) (j+1))
            (nativeStreamingPatternRefinedPairTerminalTest (nativeStreamingEdgeSubdivision j) T
              (finiteCascadeFuturePairTree (j+1))
              (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v)
              (nativeStreamingDefectSpinTest T F l))
  | .future (.edge e r) j l =>
    nativeStreamingSourceSixBracket
            D μ a
            (nativeStreamingPairObservationSchedule q e.depth j r l)
            (finiteCascadeFutureVertexGraft
              (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
                (nativeStreamingPairObservationIndex e.depth j r l))
              (observationRefinementDepth nativeStreamingPairObservationSubdivision j +
                nativeStreamingPairObservationIndex j e.depth l r + 1))
            (nativeStreamingPatternRefinedPairTerminalTest nativeStreamingPairObservationSubdivision T
              (finiteCascadeFuturePairTree (observationRefinementDepth nativeStreamingPairObservationSubdivision j +
                nativeStreamingPairObservationIndex j e.depth l r + 1))
              (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
                (nativeStreamingPairObservationIndex e.depth j r l)) (nativeStreamingDefectSpinTest T F l))
  | .normalizer l =>
    (nativeStreamingSourceSixBracket D μ a q T F *
              nativeStreamingOldTerminalExpectation D μ a (anisotropicBinaryObservationSchedule l)
                anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l) +
            nativeStreamingOldTerminalExpectation D μ a q T F *
              nativeStreamingSourceSixBracket D μ a (anisotropicBinaryObservationSchedule l)
                anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l))

theorem hasDerivWithinAt_nativeStreamingPattern_source_response
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (P : NativeStreamingAttachmentPattern T) (hP : nativeStreamingPatternValid q P)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F P)
      ((followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F P) (Icc (0:ℝ) 1) u := by
  cases P with
  | original i k =>
      exact hasDerivWithinAt_nativeStreamingPattern_original_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F i k u hu
  | originalFresh i o =>
      cases o with
      | vertex v =>
          exact hasDerivWithinAt_nativeStreamingPattern_originalFresh_vertex_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F i v u hu
      | edge e r =>
          exact hasDerivWithinAt_nativeStreamingPattern_originalFresh_edge_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F i e r hP u hu
  | current o =>
      cases o with
      | vertex v =>
          exact hasDerivWithinAt_nativeStreamingPattern_current_vertex_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F v u hu
      | edge e r =>
          exact hasDerivWithinAt_nativeStreamingPattern_current_edge_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F e r hP u hu
  | cross o p =>
      cases o with
      | vertex v =>
          cases p with
          | vertex w =>
              exact hasDerivWithinAt_nativeStreamingPattern_cross_vertices_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F v w u hu
          | edge e r =>
              exact hasDerivWithinAt_nativeStreamingPattern_cross_vertex_edge_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F v e r hP.2 u hu
      | edge e r =>
          cases p with
          | vertex v =>
              exact hasDerivWithinAt_nativeStreamingPattern_cross_edge_vertex_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F e v r hP.1 u hu
          | edge f l =>
              exact hasDerivWithinAt_nativeStreamingPattern_cross_edges_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F e f r l hP.1 hP.2 u hu
  | future o j l =>
      cases o with
      | vertex v =>
          exact hasDerivWithinAt_nativeStreamingPattern_future_vertex_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F v j l hP.2 u hu
      | edge e r =>
          exact hasDerivWithinAt_nativeStreamingPattern_future_edge_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F e r j l hP.1 hP.2 u hu
  | normalizer l =>
      exact hasDerivWithinAt_nativeStreamingPattern_normalizer_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F l u hu

end QuantitativeFollowup
