module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairProbability
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMovingTerminalMoments

@[expose] public section

/-! Pull two ancestral observations back to one fixed free measure.
The actual equal-time diagonal is retained, and the selected indices
stabilize under the prescribed-atom quantizer before the genuine
moving-profile genealogical convergence is applied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

 theorem nativeStreaming_preservingRound_closed_bounds (S : Finset Paper.Overlap)
    (N : ℕ) (b c r : Paper.Overlap) (hb : b∈S) (hc : c∈S)
    (hr : b≤r ∧ r≤c) :
    b≤FRSB.preservingRound S N r ∧ FRSB.preservingRound S N r≤c := by
  constructor
  · apply le_of_not_gt
    intro h
    exact (not_lt_of_ge hr.1) ((FRSB.preservingRound_lt_iff S N r b hb).mp h)
  · exact (FRSB.preservingRound_le_iff S N r c hc).mpr hr.2

 theorem nativeStreamingPairObservationIndex_round_eventually (S : Finset Paper.Overlap)
    (de df : ℕ) (r l : Paper.Overlap) :
    ∀ᶠN in atTop,nativeStreamingPairObservationIndex de df
      (FRSB.preservingRound S N r) (FRSB.preservingRound S N l)=
        nativeStreamingPairObservationIndex de df r l := by
  filter_upwards [nativeStreaming_round_lt_eventually S r l] with N hN
  unfold nativeStreamingPairObservationIndex
  simp only [hN]

 def nativeStreamingEdgePairProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T) (r l : Paper.Overlap) :=
    nativeStreamingEdgePairProbabilityFixed D μ a q T e f
      (nativeStreamingPairObservationIndex e.depth f.depth r l)
      (nativeStreamingPairObservationIndex f.depth e.depth l r) r l

 theorem tendsto_nativeStreamingEdgePairProbability_preserving
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap)
    (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (r l : Paper.Overlap)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (f.depth+1)≤l ∧ l≤q f.depth) :
    Tendsto (fun N=>nativeStreamingEdgePairProbability D (FRSB.preservingMeasure μ S N)
      a q T e f (FRSB.preservingRound S N r) (FRSB.preservingRound S N l)) atTop
        (𝓝 (nativeStreamingEdgePairProbability D μ a q T e f r l)) := by
  have hfixed := tendsto_nativeStreamingEdgePairProbabilityFixed D
    (FRSB.tendsto_preservingMeasure μ S) a q hq T e f
    (nativeStreamingPairObservationIndex e.depth f.depth r l)
    (nativeStreamingPairObservationIndex f.depth e.depth l r)
    (FRSB.tendsto_preservingRound S r) (FRSB.tendsto_preservingRound S l)
    (fun N=>nativeStreaming_preservingRound_closed_bounds S N _ _ r heroot hechild hr)
    (fun N=>nativeStreaming_preservingRound_closed_bounds S N _ _ l hfroot hfchild hl) hr hl
  apply Tendsto.congr' _ hfixed
  filter_upwards [nativeStreamingPairObservationIndex_round_eventually S e.depth f.depth r l,
    nativeStreamingPairObservationIndex_round_eventually S f.depth e.depth l r] with N he hf
  simp only [nativeStreamingEdgePairProbability,he,hf]

 theorem tendsto_nativeStreamingEdgePairMovingMoment_preserving
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap)
    (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (r l : Paper.Overlap)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (f.depth+1)≤l ∧ l≤q f.depth)
    (GN : ℕ→TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Tendsto (fun N=>GN N σ) atTop (𝓝 (G σ))) :
    Tendsto (fun N=>nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbability D (FRSB.preservingMeasure μ S N)
        a q T e f (FRSB.preservingRound S N r) (FRSB.preservingRound S N l)) (GN N)) atTop
      (𝓝 (nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgePairProbability D μ a q T e f r l) G)) :=
  tendsto_nativeStreamingMovingTerminalMarkMoment
    (tendsto_nativeStreamingEdgePairProbability_preserving D μ S a q hq T e f r l
      heroot hechild hfroot hfchild hr hl) GN G hG

end QuantitativeFollowup
