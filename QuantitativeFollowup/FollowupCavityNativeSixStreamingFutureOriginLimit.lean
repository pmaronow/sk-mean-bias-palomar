module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginIntegralLimits
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexFutureHalfClosedFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureOriginMoments

@[expose] public section

/-! The whole strict-future source term passes to an arbitrary profile.
Every fixed observation cell and both genuine ancestral marks are retained;
bounded product integrability supplies the finite-sum interchange. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128

theorem tendsto_nativeStreamingSourceFutureTerm
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hcuts : ∀j, j≤J → q j∈S)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    Tendsto (fun N => nativeStreamingSourceFutureTerm D (FRSB.preservingMeasure μ S N)
      a q T F) atTop (𝓝 (nativeStreamingSourceFutureTerm D μ a q T F)) := by
  classical
  let C : ℝ := ∑σ : TerminalSpins (Configuration (n+1)) T, |F σ|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hF (σ : TerminalSpins (Configuration (n+1)) T) : |F σ|≤C :=
    Finset.single_le_sum (f := fun σ => |F σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
  unfold nativeStreamingSourceFutureTerm
  apply tendsto_nativeStreamingOriginWeightIntegral (fun N => FRSB.preservingMeasure μ S N)
    μ a q T (fun _ => a) a tendsto_const_nhds
  · intro j hj
    simp_rw [FRSB.preservingMeasure_cdf_mass μ S _ _ (hcuts j hj)]
    exact tendsto_const_nhds
  · intro v
    unfold nativeStreamingPatternFutureIntegral
    apply tendsto_finset_sum (Finset.range J)
    intro j hj
    have hj' : j<J := Finset.mem_range.mp hj
    let G := fun l => nativeStreamingDefectSpinTest T F l
    have hc (σ) : Continuous (fun l => G l σ) :=
      continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_id σ
    have H := tendsto_nativeStreamingVertexFutureFamilyHalfClosedFreeIntegral D μ a ha hμ
      q hq T v j S hzero (hcuts (j+1) (by omega)) (hcuts j hj'.le)
      (hcuts v.depth v.depth_le) (fun _ => G) G (fun _ σ => hc σ)
      (fun l σ => (hc σ).tendsto l |>.comp (FRSB.tendsto_preservingRound S l))
      (2*C) (by linarith) (fun _ l σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
    simpa only [integral_nativeStreamingVertexFutureFamilyHalfClosedMoment,
      nativeStreamingPatternMoment, nativeStreamingOriginFutureProbability,
      nativeStreamingOriginLevel] using H
  · intro e
    have hIntegralSum (μ' : Paper.ParisiMeasure) :
        (∫r in Ioc (q (e.depth+1)) (q e.depth),
          nativeStreamingPatternFutureIntegral D μ' a q T F (.edge e r)
            ∂parisiFreeMeasure μ' a) =
          ∑j∈Finset.range J, ∫r in Ioc (q (e.depth+1)) (q e.depth),
            ∫l in Ioc (q (j+1)) (q j), if r<l then
              nativeStreamingPatternMoment D μ' a q T F (.future (.edge e r) j l)
            else 0 ∂parisiFreeMeasure μ' a ∂parisiFreeMeasure μ' a := by
      simp only [nativeStreamingPatternFutureIntegral, nativeStreamingOriginLevel]
      exact integral_finset_sum (Finset.range J) (fun j _ =>
        integrable_nativeStreamingEdgeFuturePattern_row D μ' a q hq T e j S F C hC hF)
    simp_rw [hIntegralSum]
    apply tendsto_finset_sum (Finset.range J)
    intro j hj
    have hj' : j<J := Finset.mem_range.mp hj
    let G := fun z : Paper.Overlap × Paper.Overlap => nativeStreamingDefectSpinTest T F z.2
    have hc (σ) : Continuous (fun z => G z σ) :=
      continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_snd σ
    have H := tendsto_nativeStreamingEdgeFutureFamilyHalfClosedFreeIntegral D μ a ha hμ
      q hq T e j S hzero (hcuts (e.depth+1) (by have := e.depth_lt; omega))
      (hcuts e.depth e.depth_lt.le) (hcuts (j+1) (by omega)) (hcuts j hj'.le)
      (fun _ => G) G (fun _ σ => hc σ)
      (fun z σ => (hc σ).tendsto z |>.comp
        ((FRSB.tendsto_preservingRound S z.1).prodMk_nhds (FRSB.tendsto_preservingRound S z.2)))
      (2*C) (by linarith) (fun _ z σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
    have aliasPair (μ' : Paper.ParisiMeasure) :=
      nativeStreamingEdgeFutureFamilyHalfClosedIntegral_eq_Ioc D μ' a q hq T e j S G hc
        (2*C) (by linarith) (fun z σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
    simpa only [aliasPair, nativeStreamingPatternMoment, nativeStreamingOriginFutureProbability] using H

end QuantitativeFollowup
