module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeFutureHalfClosedFamilyIntegral

@[expose] public section

/-! The strict future row has genuine product integrability. In particular
its edge sections can be integrated before a finite observation-cell sum;
the strict future condition keeps diagonal atoms out for the stated reason. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem integrable_nativeStreamingEdgeFutureTerminalMoment_Ioc_prod
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (j : ℕ) (S : Finset Paper.Overlap)
    (G : Paper.Overlap × Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun z => G z σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀z σ, |G z σ|≤C) :
    Integrable (fun z : Paper.Overlap × Paper.Overlap => if z.1<z.2 then
      nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgeFutureProbability D μ a q T e j z.1 z.2) (G z) else 0)
      (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
        ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) := by
  have hi : Integrable (nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q T e j S G)
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) :=
    (integrable_const C).mono'
      (measurable_nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q hq T e j S G hG).aestronglyMeasurable
      (.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using
          nativeStreamingEdgeFutureFamilyHalfClosedMoment_abs_le D μ a q T e j S G C hC hbound z)
  rw [Measure.prod_restrict]
  apply hi.restrict.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
  have he : q (e.depth+1)<z.1 ∧ z.1≤q e.depth := hz.1
  have hf : q (j+1)<z.2 ∧ z.2≤q j := hz.2
  simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,
    nativeStreamingEdgeFutureHalfClosedCondition, he, hf, true_and]

theorem integrable_nativeStreamingEdgeFuturePattern_row
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (j : ℕ) (S : Finset Paper.Overlap)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ, |F σ|≤C) :
    Integrable (fun r => ∫l in Ioc (q (j+1)) (q j), if r<l then
      nativeStreamingPatternMoment D μ a q T F (.future (.edge e r) j l) else 0
        ∂parisiFreeMeasure μ a)
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  have hi := integrable_nativeStreamingEdgeFutureTerminalMoment_Ioc_prod D μ a q hq T e j S
    (fun z => nativeStreamingDefectSpinTest T F z.2)
    (fun σ => continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_snd σ)
    (2*C) (by linarith) (fun z σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
  simpa only [nativeStreamingPatternMoment, nativeStreamingOriginFutureProbability] using
    hi.integral_prod_left

end QuantitativeFollowup
