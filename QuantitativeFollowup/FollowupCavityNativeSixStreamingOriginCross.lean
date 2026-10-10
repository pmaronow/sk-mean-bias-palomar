module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOrigin
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexPairContinuity
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairProbabilityPhysical
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairPreservingLimit

@[expose] public section

/-! Cross attachments retain their actual two locations.  A branch/edge
pair uses the genuine enlarged observation law; reversing its locations
swaps only the two fresh terminal marks and keeps every old record. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def nativeStreamingOriginCrossProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) : NativeStreamingOrigin T→NativeStreamingOrigin T→
    ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×
        (Configuration n×Configuration n))
  | .vertex v, .vertex w => nativeStreamingCrossVertexProbability D μ a q T v w
  | .edge e r, .vertex v => nativeStreamingEdgeVertexPairProbability D μ a q T e v r
  | .vertex v, .edge e r =>
      (nativeStreamingEdgeVertexPairProbability D μ a q T e v r).map
        (fun z => (z.1,(z.2.2,z.2.1)))
  | .edge e r, .edge f l => nativeStreamingEdgePairProbability D μ a q T e f r l

theorem nativeStreamingOriginCrossProbability_vertex_vertex
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T) :
    (nativeStreamingOriginCrossProbability D μ a q T (.vertex v) (.vertex w) : Measure _)=
      nativeStreamingCrossVertexLaw D μ a q T v w :=
  nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero T v w

theorem nativeStreamingOriginCrossProbability_edge_edge
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hq : Antitone q) (hzero : q 0=1) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth)
    (r l : Paper.Overlap)
    (hrange : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hlrange : q (f.depth+1)≤l ∧ l≤q f.depth)
    (hr : Q (observationRefinementDepth d e.depth+p+1)=r)
    (hl : Q (observationRefinementDepth d f.depth+k+1)=l) :
    ((nativeStreamingCrossVertexProbability D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)).map
        (fun z => ((z.1.1,observationRefinementProject d T z.1.2),z.2)))=
      nativeStreamingOriginCrossProbability D μ a q T (.edge e r) (.edge f l) := by
  exact nativeStreamingEdgePairProbability_refinement_physical D μ a q Q d hq hzero hQ hlevels
    T e f p k hp hk r l hrange hlrange hr hl

end QuantitativeFollowup
