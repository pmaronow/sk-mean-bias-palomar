module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairMomentMeasurable

@[expose] public section

/-! The genuine cross-edge mark integrals converge against the fixed
product of free measures. All prescribed cuts and every equal-mark
atom are preserved before dominated convergence is used. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

 theorem nativeStreamingEdgePairMaskedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) :
    |nativeStreamingEdgePairMaskedMoment D μ a q T e f S G z|≤nativeStreamingTerminalMarkBound T G := by
  classical
  unfold nativeStreamingEdgePairMaskedMoment
  split_ifs
  · exact nativeStreamingTerminalMarkMoment_abs_le _ G
  · simpa only [abs_zero] using nativeStreamingTerminalMarkBound_nonneg T G

 theorem nativeStreamingEdgePairOpenCondition_preserving (S : Finset Paper.Overlap)
    (N : ℕ) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (e f : NativeStreamingEdge T)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (z : Paper.Overlap×Paper.Overlap) :
    nativeStreamingEdgePairOpenCondition q e f S
      (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) ↔
        nativeStreamingEdgePairOpenCondition q e f S z := by
  simp only [nativeStreamingEdgePairOpenCondition,
    FRSB.preservingRound_gt_iff S N z.1 _ heroot,
    FRSB.preservingRound_lt_iff S N z.1 _ hechild,
    FRSB.preservingRound_gt_iff S N z.2 _ hfroot,
    FRSB.preservingRound_lt_iff S N z.2 _ hfchild,
    nativeStreaming_round_mem_prescribed_iff]

 theorem nativeStreamingEdgePairMaskedMoment_preserving_tendsto (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) :
    Tendsto (fun N=>nativeStreamingEdgePairMaskedMoment D (FRSB.preservingMeasure μ S N)
      a q T e f S G (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2)) atTop
        (𝓝 (nativeStreamingEdgePairMaskedMoment D μ a q T e f S G z)) := by
  classical
  have hm (N : ℕ) := nativeStreamingEdgePairOpenCondition_preserving S N q T e f
    heroot hechild hfroot hfchild z
  by_cases hz : nativeStreamingEdgePairOpenCondition q e f S z
  · have hp := tendsto_nativeStreamingTerminalMarkMoment
      (tendsto_nativeStreamingEdgePairProbability_preserving D μ S a q hq T e f z.1 z.2
        heroot hechild hfroot hfchild ⟨hz.1.1.le,hz.1.2.1.le⟩
        ⟨hz.2.1.le,hz.2.2.1.le⟩) G
    simpa only [nativeStreamingEdgePairMaskedMoment,hm,hz,ite_true] using hp
  · simpa only [nativeStreamingEdgePairMaskedMoment,hm,hz,ite_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))

 theorem tendsto_nativeStreamingEdgePairMarkedFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e f : NativeStreamingEdge T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ) :
    Tendsto (fun N=>∫z,nativeStreamingEdgePairMaskedMoment D (FRSB.preservingMeasure μ S N)
      a q T e f S G z ∂(parisiFreeMeasure (FRSB.preservingMeasure μ S N) a).prod
        (parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)) atTop
      (𝓝 (∫z,nativeStreamingEdgePairMaskedMoment D μ a q T e f S G z
        ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a))) :=
  nativeStreaming_free_pair_integral_tendsto μ S hzero a ha hμ _ _
    (fun N=>measurable_nativeStreamingEdgePairMaskedMoment D _ a q hq T e f S G)
    (nativeStreamingTerminalMarkBound T G) (nativeStreamingTerminalMarkBound_nonneg T G)
    (fun N z=>nativeStreamingEdgePairMaskedMoment_abs_le D _ a q T e f S G z)
    (fun r l=>nativeStreamingEdgePairMaskedMoment_preserving_tendsto D μ a q hq T e f S
      heroot hechild hfroot hfchild G (r,l))

end QuantitativeFollowup
