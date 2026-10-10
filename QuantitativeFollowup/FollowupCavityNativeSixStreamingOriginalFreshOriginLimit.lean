module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginIntegralLimits
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeHalfClosedFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingBranchMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket

@[expose] public section

/-! The entire actual original/fresh source term passes to arbitrary
profiles. Its vertex laws, fixed right masses and every halfclosed edge
integral are proved to converge before the recursive weight is consumed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem tendsto_nativeStreamingOriginalFreshOriginIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hcuts : ∀j, j≤J → q j∈S) (i : ObservationLeaf T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ, |F σ|≤C) :
    Tendsto (fun N => nativeStreamingOriginWeightIntegral (FRSB.preservingMeasure μ S N)
      a q T a (fun o => nativeStreamingPatternMoment D (FRSB.preservingMeasure μ S N)
        a q T F (.originalFresh i o))) atTop
      (𝓝 (nativeStreamingOriginWeightIntegral μ a q T a
        (fun o => nativeStreamingPatternMoment D μ a q T F (.originalFresh i o)))) := by
  apply tendsto_nativeStreamingOriginWeightIntegral (fun N => FRSB.preservingMeasure μ S N)
    μ a q T (fun _ => a) a tendsto_const_nhds
  · intro j hj
    have he (N : ℕ) := FRSB.preservingMeasure_cdf_mass μ S N (q j) (hcuts j hj)
    simp_rw [he]
    exact tendsto_const_nhds
  · intro v
    simpa only [nativeStreamingPatternMoment, nativeStreamingOriginSingleProbability,
      nativeStreamingOriginCommonClock] using
      tendsto_nativeStreamingVertexSingleMoment D (FRSB.tendsto_preservingMeasure μ S)
        a q hq T v (nativeStreamingOriginalFreshSpinTest T F i
          (q (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v)))
  · intro e
    let c := finiteCascadeCommonPathDepth T (observationLeafVertex T i)
      (nativeStreamingEdgeChildVertex e)
    let G := fun r => nativeStreamingOriginalFreshSpinTest T F i
      (nativeStreamingOldSelectedCommonClock c e.depth r (q c))
    have hc (σ) : Continuous (fun r => G r σ) :=
      continuous_nativeStreamingOriginalFreshSpinTest_clock T F i _
        (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ
    have H := tendsto_nativeStreamingEdgeSingleFamilyHalfClosedFreeIntegral D μ a ha hμ
      q hq T e S hzero (hcuts (e.depth+1) (Nat.succ_le_of_lt e.depth_lt)) (hcuts e.depth e.depth_lt.le)
      (fun _ => G) G (fun _ σ => hc σ)
      (fun r σ => (hc σ).tendsto r |>.comp (FRSB.tendsto_preservingRound S r))
      (2*C) (by linarith) (fun _ r σ => nativeStreamingOriginalFreshSpinTest_abs_le
        T F C hC hF i _ σ)
    simpa only [integral_nativeStreamingEdgeSingleFamilyHalfClosedMoment,
      nativeStreamingPatternMoment, nativeStreamingOriginSingleProbability,
      nativeStreamingOriginCommonClock] using H

theorem tendsto_nativeStreamingSourceOriginalFreshTerm
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hcuts : ∀j, j≤J → q j∈S)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    Tendsto (fun N => nativeStreamingSourceOriginalFreshTerm D
      (FRSB.preservingMeasure μ S N) a q T F) atTop
      (𝓝 (nativeStreamingSourceOriginalFreshTerm D μ a q T F)) := by
  classical
  let C : ℝ := ∑σ : TerminalSpins (Configuration (n+1)) T, |F σ|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hF (σ : TerminalSpins (Configuration (n+1)) T) : |F σ|≤C :=
    Finset.single_le_sum (f := fun σ => |F σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
  unfold nativeStreamingSourceOriginalFreshTerm
  exact (tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_nativeStreamingOriginalFreshOriginIntegral D μ a ha hμ q hq T S hzero hcuts
      i F C hC hF)).const_mul (-2)

end QuantitativeFollowup
