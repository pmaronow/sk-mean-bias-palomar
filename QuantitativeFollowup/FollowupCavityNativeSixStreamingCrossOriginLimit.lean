module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossIntegralLimits
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossOriginMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingBranchMoments

@[expose] public section

/-! The genuine whole cross source term passes under the preserving
profile approximation. Both weights refer to the original tree. The
four vertex/edge cases retain all free-measure atoms; Fubini is discharged
from the actual bounded two-mark integrability, including the diagonal. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

 theorem tendsto_nativeStreamingSourceCrossTerm
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hcuts : ∀j, j≤J → q j∈S)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    Tendsto (fun N => nativeStreamingSourceCrossTerm D (FRSB.preservingMeasure μ S N)
      a q T F) atTop (𝓝 (nativeStreamingSourceCrossTerm D μ a q T F)) := by
  classical
  let C : ℝ := ∑σ : TerminalSpins (Configuration (n+1)) T, |F σ|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hF (σ : TerminalSpins (Configuration (n+1)) T) : |F σ|≤C :=
    Finset.single_le_sum (f := fun σ => |F σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
  have EV (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) :
      Tendsto (fun N => ∫r in Ioc (q (e.depth+1)) (q e.depth),
        nativeStreamingPatternMoment D (FRSB.preservingMeasure μ S N) a q T F
          (.cross (.edge e r) (.vertex v)) ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)
        atTop (𝓝 (∫r in Ioc (q (e.depth+1)) (q e.depth),
          nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.vertex v))
            ∂parisiFreeMeasure μ a)) := by
    let c := finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)
    let G := fun r => nativeStreamingDefectSpinTest T F
      (nativeStreamingOldSelectedCommonClock c e.depth r (q c))
    have hc (σ) : Continuous (fun r => G r σ) :=
      continuous_nativeStreamingDefectSpinTest_clock T F _
        (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ
    have H := tendsto_nativeStreamingEdgeVertexFamilyHalfClosedFreeIntegral D μ a ha hμ
      q hq T e v S hzero (hcuts (e.depth+1) (by have := e.depth_lt; omega))
      (hcuts e.depth e.depth_lt.le) (fun _ => G) G (fun _ σ => hc σ)
      (fun r σ => (hc σ).tendsto r |>.comp (FRSB.tendsto_preservingRound S r))
      (2*C) (by linarith) (fun _ r σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
    simpa only [integral_nativeStreamingEdgeVertexFamilyHalfClosedMoment,
      nativeStreamingPatternMoment, nativeStreamingOriginCrossProbability,
      nativeStreamingOriginCommonClock] using H
  have EVint (μ' : Paper.ParisiMeasure) (e : NativeStreamingEdge T)
      (v : FiniteCascadeRecordVertex T) :
      Integrable (fun r => nativeStreamingPatternMoment D μ' a q T F
        (.cross (.edge e r) (.vertex v)))
        ((parisiFreeMeasure μ' a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
    let c := finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)
    let G := fun r => nativeStreamingDefectSpinTest T F
      (nativeStreamingOldSelectedCommonClock c e.depth r (q c))
    simpa only [nativeStreamingPatternMoment, nativeStreamingOriginCrossProbability,
      nativeStreamingOriginCommonClock] using
      integrable_nativeStreamingEdgeVertexTerminalMoment_Ioc D μ' a q hq T e v G
        (fun σ => continuous_nativeStreamingDefectSpinTest_clock T F _
          (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ)
        (2*C) (by linarith) (fun r σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
  have EEint (μ' : Paper.ParisiMeasure) (e f : NativeStreamingEdge T) :
      Integrable (fun z : Paper.Overlap × Paper.Overlap => nativeStreamingPatternMoment
        D μ' a q T F (.cross (.edge e z.1) (.edge f z.2)))
        (((parisiFreeMeasure μ' a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
          ((parisiFreeMeasure μ' a).restrict (Ioc (q (f.depth+1)) (q f.depth)))) := by
    let c := finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e)
      (nativeStreamingEdgeChildVertex f)
    let G := fun z : Paper.Overlap × Paper.Overlap => nativeStreamingDefectSpinTest T F
      (nativeStreamingSelectedCommonClock c e.depth f.depth z.1 z.2 (q c))
    simpa only [nativeStreamingPatternMoment, nativeStreamingOriginCrossProbability,
      nativeStreamingOriginCommonClock] using
      integrable_nativeStreamingEdgePairTerminalMoment_Ioc_prod D μ' a q hq T e f S G
        (continuous_nativeStreamingEdgePairDefectSpinTest T F c e.depth f.depth (q c))
        (2*C) (by linarith) (fun z σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
  unfold nativeStreamingSourceCrossTerm
  apply tendsto_nativeStreamingOriginPairWeightIntegral
    (fun N => FRSB.preservingMeasure μ S N) μ a q T T
    (fun _ => a) (fun _ => a) a a tendsto_const_nhds tendsto_const_nhds
  · intro j hj
    simp_rw [FRSB.preservingMeasure_cdf_mass μ S _ _ (hcuts j hj)]
    exact tendsto_const_nhds
  · intro j hj
    simp_rw [FRSB.preservingMeasure_cdf_mass μ S _ _ (hcuts j hj)]
    exact tendsto_const_nhds
  · intro v w
    simpa only [nativeStreamingPatternMoment, nativeStreamingOriginCrossProbability,
      nativeStreamingOriginCommonClock] using
      tendsto_nativeStreamingTerminalMarkMoment
        (tendsto_nativeStreamingCrossVertexProbability D (FRSB.tendsto_preservingMeasure μ S)
          a (fun _ => q) q T v w (fun _ _ => tendsto_const_nhds)
          (fun _ p _ => hq (Nat.le_succ p)) (fun p _ => hq (Nat.le_succ p)))
        (nativeStreamingDefectSpinTest T F (q (finiteCascadeCommonPathDepth T v w)))
  · intro v f
    simp_rw [nativeStreamingPatternMoment_cross_vertex_edge]
    exact EV f v
  · exact EV
  · intro e f
    let c := finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e)
      (nativeStreamingEdgeChildVertex f)
    let G := fun z : Paper.Overlap × Paper.Overlap => nativeStreamingDefectSpinTest T F
      (nativeStreamingSelectedCommonClock c e.depth f.depth z.1 z.2 (q c))
    have hc := continuous_nativeStreamingEdgePairDefectSpinTest T F c e.depth f.depth (q c)
    have H := tendsto_nativeStreamingEdgePairFamilyHalfClosedFreeIntegral D μ a ha hμ
      q hq T e f S hzero (hcuts (e.depth+1) (by have := e.depth_lt; omega))
      (hcuts e.depth e.depth_lt.le) (hcuts (f.depth+1) (by have := f.depth_lt; omega))
      (hcuts f.depth f.depth_lt.le) (fun _ => G) G (fun _ σ => hc σ)
      (fun z σ => (hc σ).tendsto z |>.comp
        ((FRSB.tendsto_preservingRound S z.1).prodMk_nhds (FRSB.tendsto_preservingRound S z.2)))
      (2*C) (by linarith) (fun _ z σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
    have hIntegralOrder (μ' : Paper.ParisiMeasure) :
        (∫z, nativeStreamingEdgePairFamilyHalfClosedMoment D μ' a q T e f S G z
          ∂(parisiFreeMeasure μ' a).prod (parisiFreeMeasure μ' a)) =
          ∫l in Ioc (q (f.depth+1)) (q f.depth),
            ∫r in Ioc (q (e.depth+1)) (q e.depth),
              nativeStreamingPatternMoment D μ' a q T F (.cross (.edge e r) (.edge f l))
                ∂parisiFreeMeasure μ' a ∂parisiFreeMeasure μ' a := by
      rw [nativeStreamingEdgePairFamilyHalfClosedIntegral_eq_Ioc D μ' a q hq T e f S G hc
        (2*C) (by linarith) (fun z σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)]
      change (∫r in Ioc (q (e.depth+1)) (q e.depth),
        ∫l in Ioc (q (f.depth+1)) (q f.depth), nativeStreamingPatternMoment D μ' a q T F
          (.cross (.edge e r) (.edge f l)) ∂parisiFreeMeasure μ' a ∂parisiFreeMeasure μ' a) = _
      exact integral_integral_swap (EEint μ' e f)
    simpa only [hIntegralOrder] using H
  · intro N
    exact EVint (FRSB.preservingMeasure μ S N)
  · intro N
    exact EEint (FRSB.preservingMeasure μ S N)
  · exact EVint μ
  · exact EEint μ

end QuantitativeFollowup
