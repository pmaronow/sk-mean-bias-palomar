module
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceContracts
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceWeight

@[expose] public section

/-! The genuine inner cross attachment integral is itself coherent on
all original zero-time components. Joint physical-cell integrability is
proved from the actual two-mark law before invoking Fubini. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

theorem integrableOn_nativeStreamingCoalescedCrossWeight
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ, |F σ|≤C)
    (s : ℝ) (e : NativeStreamingEdge T) :
    IntegrableOn (fun r => nativeStreamingOriginWeightIntegral μ a q T s
      (fun p => nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) p)))
      (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  apply (nativeStreamingOriginWeightIntegral_parameter_fubini
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))
    μ a q T s (fun r p => nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) p))
    (fun v => integrableOn_nativeStreamingCoalescedCrossVertex D μ a q hq T F e v) ?_).1
  intro f
  let c := finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
  let G := fun z : Paper.Overlap × Paper.Overlap => nativeStreamingDefectSpinTest T F
    (nativeStreamingSelectedCommonClock c e.depth f.depth z.1 z.2 (q c))
  have hG : ∀σ, Continuous (fun z => G z σ) := fun σ =>
    continuous_nativeStreamingDefectSpinTest_clock T F _
      (continuous_nativeStreamingSelectedCommonClock c e.depth f.depth (q c)) σ
  exact integrable_nativeStreamingEdgePairTerminalMoment_Ioc_prod D μ a q hq T e f ∅ G hG
    (2*C) (by positivity) (fun z σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)

theorem nativeCoalescedOriginCoherent_cross_weight
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ, |F σ|≤C) (s : ℝ) :
    nativeCoalescedOriginCoherent μ a q T (fun o => nativeStreamingOriginWeightIntegral μ a q T s
      (fun p => nativeStreamingPatternMoment D μ a q T F (.cross o p))) := by
  refine nativeCoalescedOriginCoherent_of_edges_root_coherent μ a q T _ ?_ ?_ ?_
    (integrableOn_nativeStreamingCoalescedCrossWeight D μ a q hq T F C hC hF s)
  · exact nativeStreamingRootCoherent_originWeightIntegral μ a q T T s _
      (fun p _ => nativeStreamingPatternMoment_cross_left_origin_root_coherent D μ a q T F p)
  · intro e he
    exact nativeStreamingOriginWeightIntegral_congr_valid μ a q T s _ _ (fun p hp =>
      (nativeStreamingPatternMoment_cross_valid_edge_same_time_left D μ a q hq hzero T F e he p hp).symm)
  · intro e
    exact nativeStreamingOriginWeightIntegral_congr_valid μ a q T s _ _ (fun p hp =>
      nativeStreamingPatternMoment_cross_valid_upper_left D μ a q hq hzero T F e p hp)

end QuantitativeFollowup
