module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOrigin
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFuturePairContinuity
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeFuturePreservingLimit

@[expose] public section

/-! A strict-future attachment records both its original location and its
actual future observation cell.  The branch case inserts that future time
before attaching the genuine shared continuation; the edge case retains
the selected ancestor together with the future observation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128

def nativeStreamingOriginFutureProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) : NativeStreamingOrigin T → ℕ → Paper.Overlap →
    ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n))
  | .vertex v, j, l => nativeStreamingInsertedFuturePairProbability D μ a q T v j l
  | .edge e r, j, l => nativeStreamingEdgeFutureProbability D μ a q T e j r l

theorem nativeStreamingOriginFutureProbability_vertex_eq_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (j : ℕ) (hj : j < v.depth) (l : Paper.Overlap)
    (hl : q (j + 1) ≤ l ∧ l ≤ q j) :
    (nativeStreamingOriginFutureProbability D μ a q T (.vertex v) j l : Measure _) =
      nativeStreamingFuturePairLaw D μ a q T v l :=
  nativeStreamingInsertedFuturePairProbability_eq_law D μ a q hq hzero T v j hj l hl

theorem nativeStreamingOriginFutureNewMarkCount_le_two
    {T : FiniteTerminalGenealogy J} (o : NativeStreamingOrigin T) :
    nativeStreamingOriginNewMarkCount o + 1 ≤ 2 := by
  have ho := nativeStreamingOriginNewMarkCount_le_one o
  omega

end QuantitativeFollowup
