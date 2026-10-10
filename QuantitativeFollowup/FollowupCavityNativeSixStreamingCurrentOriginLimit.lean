module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginIntegralLimits
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeHalfClosedFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingBranchMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket

@[expose] public section

/-! Passage of the complete current-pair source term. The actual CDF at
an inserted ancestral state is retained inside the free-measure integral;
at fixed vertices preserving approximation retains it exactly. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem integral_nativeStreamingEdgeCurrentCDFHalfClosedMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) :
    (∫r, nativeStreamingEdgeCurrentCDFHalfClosedMoment D μ a q T e G r
      ∂parisiFreeMeasure μ a) =
    ∫r in Ioc (q (e.depth+1)) (q e.depth), Paper.parisiCDF μ r *
      nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgeCurrentPairProbability D μ a q T e r) (G r)
      ∂parisiFreeMeasure μ a := by
  have he (r : Paper.Overlap) :
      nativeStreamingEdgeCurrentCDFHalfClosedMoment D μ a q T e G r =
      (Ioc (q (e.depth+1)) (q e.depth)).indicator
        (fun r => Paper.parisiCDF μ r * nativeStreamingTerminalMarkMoment
          (nativeStreamingEdgeCurrentPairProbability D μ a q T e r) (G r)) r := by
    by_cases hr : r ∈ Ioc (q (e.depth+1)) (q e.depth)
    · simp only [nativeStreamingEdgeCurrentCDFHalfClosedMoment,
        nativeStreamingEdgeCurrentFamilyHalfClosedMoment, Set.indicator_of_mem hr,
        if_pos (mem_Ioc.mp hr)]
    · simp only [nativeStreamingEdgeCurrentCDFHalfClosedMoment,
        nativeStreamingEdgeCurrentFamilyHalfClosedMoment, Set.indicator_of_notMem hr,
        if_neg (show ¬(q (e.depth+1)<r ∧ r≤q e.depth) from hr), mul_zero]
  simp_rw [he]
  exact integral_indicator measurableSet_Ioc

theorem tendsto_nativeStreamingSourceCurrentTerm
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hcuts : ∀j, j≤J → q j∈S)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    Tendsto (fun N => nativeStreamingSourceCurrentTerm D
      (FRSB.preservingMeasure μ S N) a q T F) atTop
      (𝓝 (nativeStreamingSourceCurrentTerm D μ a q T F)) := by
  classical
  let C : ℝ := ∑σ : TerminalSpins (Configuration (n+1)) T, |F σ|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hF (σ : TerminalSpins (Configuration (n+1)) T) : |F σ|≤C :=
    Finset.single_le_sum (f := fun σ => |F σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
  unfold nativeStreamingSourceCurrentTerm
  apply tendsto_nativeStreamingOriginWeightIntegral (fun N => FRSB.preservingMeasure μ S N)
    μ a q T (fun _ => a) a tendsto_const_nhds
  · intro j hj
    have he (N : ℕ) := FRSB.preservingMeasure_cdf_mass μ S N (q j) (hcuts j hj)
    simp_rw [he]
    exact tendsto_const_nhds
  · intro v
    have he (N : ℕ) := FRSB.preservingMeasure_cdf_mass μ S N (q v.depth)
      (hcuts v.depth v.depth_le)
    simp only [nativeStreamingOriginLevel, nativeStreamingPatternMoment,
      nativeStreamingOriginCurrentProbability]
    simp_rw [he]
    exact (tendsto_nativeStreamingTerminalMarkMoment
      (tendsto_nativeStreamingCurrentPairProbability D (FRSB.tendsto_preservingMeasure μ S)
        a (fun _ => q) q T v (fun _ _ => tendsto_const_nhds)
        (fun _ p _ => hq (Nat.le_succ p)) (fun p _ => hq (Nat.le_succ p)))
      (nativeStreamingDefectSpinTest T F (q v.depth))).const_mul _
  · intro e
    let G := fun r => nativeStreamingDefectSpinTest T F r
    have hc (σ) : Continuous (fun r => G r σ) :=
      continuous_nativeStreamingDefectSpinTest_clock T F id continuous_id σ
    have H := tendsto_nativeStreamingEdgeCurrentCDFHalfClosedIntegral D μ a ha hμ
      q hq T e S hzero (hcuts (e.depth+1) (Nat.succ_le_of_lt e.depth_lt))
      (hcuts e.depth e.depth_lt.le) (fun _ => G) G (fun _ σ => hc σ)
      (fun r σ => (hc σ).tendsto r |>.comp (FRSB.tendsto_preservingRound S r))
      (2*C) (by linarith) (fun _ r σ => nativeStreamingDefectSpinTest_abs_le
        T F C hC hF r σ)
    simpa only [integral_nativeStreamingEdgeCurrentCDFHalfClosedMoment,
      nativeStreamingPatternMoment, nativeStreamingOriginCurrentProbability,
      nativeStreamingOriginLevel] using H

end QuantitativeFollowup
