module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentPairContinuity

@[expose] public section

/-! A source mark retains its genuine attachment location. Vertex marks
use the native conditional continuation at that retained vertex; edge
marks use the actual inserted ancestor and preserve the entire old record.
The grammar does not identify a derivative with a marked expectation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128

inductive NativeStreamingOrigin (T : FiniteTerminalGenealogy J) where
  | vertex (v : FiniteCascadeRecordVertex T)
  | edge (e : NativeStreamingEdge T) (r : Paper.Overlap)

@[reducible] def nativeStreamingOriginLevel (q : ℕ→Paper.Overlap)
    {T : FiniteTerminalGenealogy J} : NativeStreamingOrigin T→Paper.Overlap
  | .vertex v => q v.depth
  | .edge _ r => r

@[reducible] def nativeStreamingOriginNewMarkCount {T : FiniteTerminalGenealogy J} :
    NativeStreamingOrigin T→ℕ
  | .vertex _ => 0
  | .edge _ _ => 1

theorem nativeStreamingOriginNewMarkCount_le_one {T : FiniteTerminalGenealogy J}
    (o : NativeStreamingOrigin T) : nativeStreamingOriginNewMarkCount o≤1 := by
  cases o <;> simp only [nativeStreamingOriginNewMarkCount] <;> omega

theorem nativeStreamingOriginPairNewMarkCount_le_two {T : FiniteTerminalGenealogy J}
    (o p : NativeStreamingOrigin T) :
    nativeStreamingOriginNewMarkCount o+nativeStreamingOriginNewMarkCount p≤2 := by
  have ho:=nativeStreamingOriginNewMarkCount_le_one o
  have hp:=nativeStreamingOriginNewMarkCount_le_one p
  omega

def nativeStreamingOriginSingleProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) : NativeStreamingOrigin T→
    ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×Configuration n)
  | .vertex v => nativeStreamingSingleVertexProbability D μ a q T v
  | .edge e r => nativeStreamingEdgeSingleMarkProbability D μ a q T e r

def nativeStreamingOriginCurrentProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) : NativeStreamingOrigin T→
    ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×(Configuration n×Configuration n))
  | .vertex v => nativeStreamingCurrentPairProbability D μ a q T v
  | .edge e r => nativeStreamingEdgeCurrentPairProbability D μ a q T e r

end QuantitativeFollowup
