module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOldTerminalMomentLimit

@[expose] public section

/-! The original-spin and independent normalizer terms pass to the native
profile through their literal terminal tests. The original diagonal defect
vanishes exactly and no pair-law or expectation limit is an assumption. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem tendsto_nativeStreamingSourceOriginalTerm
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel (n+1))
    {μN : L → Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μN l (𝓝 μ))
    (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    Tendsto (fun N => nativeStreamingSourceOriginalTerm D (μN N) a q T F) l
      (𝓝 (nativeStreamingSourceOriginalTerm D μ a q T F)) := by
  classical
  unfold nativeStreamingSourceOriginalTerm
  apply tendsto_finset_sum Finset.univ
  intro i _
  apply tendsto_finset_sum Finset.univ
  intro k _
  by_cases hik : i=k
  · simp only [nativeStreamingPatternMoment, if_pos hik]
    exact tendsto_const_nhds
  · have ht := tendsto_nativeStreamingOldTerminalExpectation D hμ a q hq T
      (fun σ => F σ * cavitySpinOverlapDefect n (q (observationCommonLevel T i k))
        (observationTerminalSpin T i σ) (observationTerminalSpin T k σ))
    simpa only [nativeStreamingPatternMoment, if_neg hik,
      nativeStreamingOldTerminalExpectation, observationTerminalSpin_record] using ht

theorem tendsto_nativeStreamingSourceNormalizerTerm
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S) :
    Tendsto (fun N => nativeStreamingSourceNormalizerTerm D
      (FRSB.preservingMeasure μ S N) a q T F) atTop
      (𝓝 (nativeStreamingSourceNormalizerTerm D μ a q T F)) := by
  simp_rw [nativeStreamingSourceNormalizerTerm_eq_independent]
  exact tendsto_nativeStreamingNormalizerPatternIntegral D μ a ha hμ q hq T F S hzero

end QuantitativeFollowup
