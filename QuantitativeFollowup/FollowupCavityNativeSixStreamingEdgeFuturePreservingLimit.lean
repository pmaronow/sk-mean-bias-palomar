module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeFutureProbability
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairPreservingLimit

@[expose] public section

/-! The true shared-future law uses the canonical chronological slots.
Prescribed edge endpoints remain fixed and the two slot indices stabilize,
including equality before the strict-future restriction is applied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def nativeStreamingEdgeFutureProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (j : ℕ)
    (r l : Paper.Overlap) :=
  nativeStreamingEdgeFutureProbabilityFixed D μ a q T e j
    (nativeStreamingPairObservationIndex e.depth j r l)
    (nativeStreamingPairObservationIndex j e.depth l r) r l

theorem tendsto_nativeStreamingEdgeFutureProbability_preserving
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap)
    (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (j : ℕ)
    (r l : Paper.Overlap)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfutureRoot : q (j+1)∈S) (hfutureChild : q j∈S)
    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (j+1)≤l ∧ l≤q j) :
    Tendsto (fun N => nativeStreamingEdgeFutureProbability D (FRSB.preservingMeasure μ S N)
      a q T e j (FRSB.preservingRound S N r) (FRSB.preservingRound S N l)) atTop
        (𝓝 (nativeStreamingEdgeFutureProbability D μ a q T e j r l)) := by
  have hfixed := tendsto_nativeStreamingEdgeFutureProbabilityFixed D
    (FRSB.tendsto_preservingMeasure μ S) a q hq T e j
    (nativeStreamingPairObservationIndex e.depth j r l)
    (nativeStreamingPairObservationIndex j e.depth l r)
    (FRSB.tendsto_preservingRound S r) (FRSB.tendsto_preservingRound S l)
    (fun N => nativeStreaming_preservingRound_closed_bounds S N _ _ r heroot hechild hr)
    (fun N => nativeStreaming_preservingRound_closed_bounds S N _ _ l hfutureRoot hfutureChild hl)
    hr hl
  apply Tendsto.congr' _ hfixed
  filter_upwards [nativeStreamingPairObservationIndex_round_eventually S e.depth j r l,
    nativeStreamingPairObservationIndex_round_eventually S j e.depth l r] with N he hf
  simp only [nativeStreamingEdgeFutureProbability,he,hf]

theorem nativeStreaming_future_cell_before_origin (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (de j : ℕ) (r l : Paper.Overlap) (hr : q (de+1)<r) (hl : l<q j)
    (hrl : r<l) : j≤de := by
  by_contra hj
  have hc := hq (show de+1≤j by omega)
  exact (not_lt_of_ge hc) ((hr.trans hrl).trans hl)

end QuantitativeFollowup
