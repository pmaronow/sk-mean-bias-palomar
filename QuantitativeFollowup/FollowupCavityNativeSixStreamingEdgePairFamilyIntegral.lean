module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairFamilyMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairMarkIntegral

@[expose] public section

/-! Pull the genuine moving terminal-test family back to the original
product free measure. Prescribed branch levels and equal-mark atoms are
retained; finite-spin bounds supply the dominated convergence estimate. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem nativeStreamingEdgePairFamilyMaskedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀z σ,|G z σ|≤C) (z : Paper.Overlap×Paper.Overlap) :
    |nativeStreamingEdgePairFamilyMaskedMoment D μ a q T e f S G z|≤C := by
  classical
  unfold nativeStreamingEdgePairFamilyMaskedMoment
  split_ifs
  · exact nativeStreamingTerminalMarkMoment_abs_le_bound _ (G z) C (hG z)
  · simpa only [abs_zero] using hC

theorem nativeStreamingEdgePairFamilyMaskedMoment_preserving_tendsto (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (GN : ℕ→Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀z σ,Tendsto (fun N=>GN N
      (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) σ) atTop (𝓝 (G z σ)))
    (z : Paper.Overlap×Paper.Overlap) :
    Tendsto (fun N=>nativeStreamingEdgePairFamilyMaskedMoment D (FRSB.preservingMeasure μ S N)
      a q T e f S (GN N) (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2)) atTop
        (𝓝 (nativeStreamingEdgePairFamilyMaskedMoment D μ a q T e f S G z)) := by
  classical
  have hm (N : ℕ) := nativeStreamingEdgePairOpenCondition_preserving S N q T e f
    heroot hechild hfroot hfchild z
  by_cases hz : nativeStreamingEdgePairOpenCondition q e f S z
  · have hp := tendsto_nativeStreamingEdgePairMovingMoment_preserving D μ S a q hq T e f z.1 z.2
      heroot hechild hfroot hfchild ⟨hz.1.1.le,hz.1.2.1.le⟩ ⟨hz.2.1.le,hz.2.2.1.le⟩
      (fun N=>GN N (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2)) (G z) (hG z)
    simpa only [nativeStreamingEdgePairFamilyMaskedMoment,hm,hz,ite_true] using hp
  · simpa only [nativeStreamingEdgePairFamilyMaskedMoment,hm,hz,ite_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))

theorem tendsto_nativeStreamingEdgePairFamilyFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e f : NativeStreamingEdge T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (GN : ℕ→Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hGN : ∀N σ,Continuous (fun z=>GN N z σ))
    (hG : ∀z σ,Tendsto (fun N=>GN N
      (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) σ) atTop (𝓝 (G z σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N z σ,|GN N z σ|≤C) :
    Tendsto (fun N=>∫z,nativeStreamingEdgePairFamilyMaskedMoment D (FRSB.preservingMeasure μ S N)
      a q T e f S (GN N) z ∂(parisiFreeMeasure (FRSB.preservingMeasure μ S N) a).prod
        (parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)) atTop
      (𝓝 (∫z,nativeStreamingEdgePairFamilyMaskedMoment D μ a q T e f S G z
        ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a))) :=
  nativeStreaming_free_pair_integral_tendsto μ S hzero a ha hμ _ _
    (fun N=>measurable_nativeStreamingEdgePairFamilyMaskedMoment D _ a q hq T e f S
      (GN N) (hGN N)) C hC
    (fun N z=>nativeStreamingEdgePairFamilyMaskedMoment_abs_le D _ a q T e f S
      (GN N) C hC (hbound N) z)
    (fun r l=>nativeStreamingEdgePairFamilyMaskedMoment_preserving_tendsto D μ a q hq T e f S
      heroot hechild hfroot hfchild GN G hG (r,l))

end QuantitativeFollowup
