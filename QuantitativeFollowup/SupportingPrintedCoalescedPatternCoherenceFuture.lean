module
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceStates
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureWeightCoherence
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeFutureEndpoint

@[expose] public section

/-! The actual weighted future callback remains coherent after zero-time
components are contracted. The strict future cut is retained exactly. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

theorem nativeStreamingFutureMaskedMoment_eq_of_clock_state
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v w : FiniteCascadeRecordVertex T) (hc : q v.depth=q w.depth)
    (hs : ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState w z.1 z.2)
    (r : Paper.Overlap) :
    (if q v.depth<r then
      (∫ z, nativeStreamingDefectSpinTest T F r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂nativeStreamingFuturePairLaw D μ a q T v r) else 0) =
      (if q w.depth<r then
        (∫ z, nativeStreamingDefectSpinTest T F r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
          ∂nativeStreamingFuturePairLaw D μ a q T w r) else 0) := by
  rw [hc]
  by_cases hr : q w.depth<r
  · simp only [hr,ite_true]
    rw [nativeStreamingFutureTerminalMoment_eq_integral D μ a q T v r,
      nativeStreamingFutureTerminalMoment_eq_integral D μ a q T w r]
    apply integral_congr_ae
    filter_upwards [hs] with z hz
    rw [hc,hz]
  · simp only [hr,ite_false]

theorem nativeStreamingPatternFutureIntegral_vertex_eq_actual
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternFutureIntegral D μ a q T F (.vertex v) =
      ∑ j ∈ Finset.range J, ∫ r in Ioc (q (j+1)) (q j), if q v.depth<r then
        (∫ z, nativeStreamingDefectSpinTest T F r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
          ∂nativeStreamingFuturePairLaw D μ a q T v r) else 0
          ∂parisiFreeMeasure μ a := by
  classical
  unfold nativeStreamingPatternFutureIntegral
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [nativeStreamingOriginLevel]
  by_cases hv : q v.depth<r
  · have hjv : j<v.depth := by
      by_contra hh
      have hle := hq (show v.depth≤j by omega)
      exact (not_lt_of_ge (hr.2.trans hle)) hv
    simp only [hv,ite_true,nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment]
    rw [nativeStreamingOriginFutureProbability_vertex_eq_law D μ a q hq hzero T v j hjv r
      ⟨hr.1.le,hr.2⟩]
  · simp only [hv,ite_false]

theorem nativeStreamingPatternFutureIntegral_edge_same_time
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth) :
    nativeStreamingPatternFutureIntegral D μ a q T F (.vertex (nativeStreamingEdgeParentVertex e)) =
      nativeStreamingPatternFutureIntegral D μ a q T F (.vertex (nativeStreamingEdgeChildVertex e)) := by
  have hc : q (nativeStreamingEdgeParentVertex e).depth=q (nativeStreamingEdgeChildVertex e).depth := by
    rw [nativeStreamingEdgeParentVertex_depth,nativeStreamingEdgeChildVertex_depth,he]
  rw [nativeStreamingPatternFutureIntegral_vertex_eq_actual D μ a q hq hzero T F,
    nativeStreamingPatternFutureIntegral_vertex_eq_actual D μ a q hq hzero T F]
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  exact .of_forall fun r => nativeStreamingFutureMaskedMoment_eq_of_clock_state D μ a q T F
    (nativeStreamingEdgeParentVertex e) (nativeStreamingEdgeChildVertex e) hc
    (nativeStreamingRecordedLaw_edge_same_time_coherent D μ a q T e he) r

end QuantitativeFollowup
