module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket

@[expose] public section

/-! A child-endpoint edge origin has exactly the old child vertex's
shared-future marked law.  The whole original record and both fresh
terminal spins are retained, including repeated observation clocks.
The strict-future cell integral preserves its actual half-closed atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem edgeFutureEndpoint_law_state_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T) (l : Paper.Overlap)
    (hv : q v.depth = q w.depth)
    (hs : ∀ᵐz ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2 = nativeStreamingVertexState w z.1 z.2) :
    nativeStreamingFuturePairLaw D μ a q T v l =
      nativeStreamingFuturePairLaw D μ a q T w l := by
  apply Measure.compProd_congr
  filter_upwards [hs] with z hz
  simp only [nativeStreamingFuturePairKernel, Kernel.comap_apply,
    Function.uncurry_def, hv, hz]

theorem nativeStreamingOriginFutureProbability_edge_child_eq_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (j : ℕ) (hj : j < e.depth) (l : Paper.Overlap)
    (hl : q (j+1) ≤ l ∧ l ≤ q j) :
    (nativeStreamingOriginFutureProbability D μ a q T (.edge e (q e.depth)) j l : Measure _) =
      nativeStreamingFuturePairLaw D μ a q T (nativeStreamingEdgeChildVertex e) l := by
  let d := nativeStreamingPairObservationSubdivision
  let Q := nativeStreamingPairObservationSchedule q e.depth j (q e.depth) l
  let p := nativeStreamingPairObservationIndex e.depth j (q e.depth) l
  let k := nativeStreamingPairObservationIndex j e.depth l (q e.depth)
  have hp : p < d e.depth := nativeStreamingPairObservationIndex_lt _ _ _ _
  have hr : q (e.depth+1) ≤ q e.depth ∧ q e.depth ≤ q e.depth :=
    ⟨hq (Nat.le_succ _), le_rfl⟩
  have hrl : q e.depth ≤ l := (hq (show j+1 ≤ e.depth by omega)).trans hl.1
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq
    e.depth j (q e.depth) l hr hl
  have hlevels : ∀i, Q (observationRefinementDepth d i) = q i :=
    nativeStreamingPairObservationSchedule_refinement q e.depth j (q e.depth) l
  have hpr : Q (observationRefinementDepth d e.depth+p+1) = q e.depth :=
    nativeStreamingPairObservationIndex_level q e.depth j (q e.depth) l
  have hkl : Q (observationRefinementDepth d j+k+1) = l :=
    nativeStreamingPairObservationIndex_second_level q e.depth j (q e.depth) l
  have hfuture : observationRefinementDepth d j+k+1 ≤
      observationRefinementDepth d e.depth+p+1 :=
    nativeStreamingPairObservationIndex_future_le e.depth j (q e.depth) l hj.le hrl
  have hphysical :
      (nativeStreamingOriginFutureProbability D μ a q T (.edge e (q e.depth)) j l : Measure _) =
        (nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
          (nativeStreamingEdgeSelectedVertex d e p) l).map
            (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2)) := by
    have H := nativeStreamingEdgeFutureProbabilityFixed_eq_kernel D μ a q hq hzero
      T e j p k hp hfuture (q e.depth) l hr hl
    change (nativeStreamingEdgeFutureProbabilityFixed D μ a q T e j p k (q e.depth) l :
        Measure ((AnisotropicObservationState n ×
          Records (AnisotropicObservationState n) (Configuration n) T) ×
            (Configuration n × Configuration n))) =
      ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1))) ⊗ₘ
          nativeStreamingEdgeObservedFutureKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1))
            (Q (observationRefinementDepth d j+k+1))).map _ at H
    rw [hpr, hkl] at H
    have Hproj := nativeStreamingEdgeSelectedFutureLaw_projection D μ a q Q d hQ
      hlevels e p hp l
    rw [hpr] at Hproj
    exact H.trans Hproj.symm
  have hv : Q (nativeStreamingEdgeSelectedVertex d e p).depth =
      Q (nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeChildVertex e)).depth := by
    rw [nativeStreamingEdgeSelectedVertex_depth d e p hp, hpr,
      nativeStreamingRefinementVertexEmbed_depth, hlevels, nativeStreamingEdgeChildVertex_depth]
  have hs : ∀ᵐz ∂anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T),
      nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d e p) z.1 z.2 =
        nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T
          (nativeStreamingEdgeChildVertex e)) z.1 z.2 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
        (nativeStreamingVertexState_measurable _))
    apply Eventually.of_forall
    intro x
    exact nativeStreamingSelected_child_endpoint_state D μ q Q d hq hQ hlevels
      T e p hp hpr x
  have Hstate := edgeFutureEndpoint_law_state_eq D μ a Q (observationRefineTree d T)
    _ _ l hv hs
  rw [hphysical, Hstate]
  exact nativeStreamingFuturePairLaw_refinement D μ a q Q d hQ hlevels T
    (nativeStreamingEdgeChildVertex e) l

theorem nativeStreamingPatternMoment_future_edge_child_endpoint
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (j : ℕ) (hj : j < e.depth) (l : Paper.Overlap)
    (hl : q (j+1) ≤ l ∧ l ≤ q j) :
    nativeStreamingPatternMoment D μ a q T F (.future (.edge e (q e.depth)) j l) =
      nativeStreamingPatternMoment D μ a q T F
        (.future (.vertex (nativeStreamingEdgeChildVertex e)) j l) := by
  simp only [nativeStreamingPatternMoment, nativeStreamingTerminalMarkMoment]
  rw [nativeStreamingOriginFutureProbability_edge_child_eq_law D μ a q hq hzero T e j hj l hl,
    nativeStreamingOriginFutureProbability_vertex_eq_law D μ a q hq hzero T
      (nativeStreamingEdgeChildVertex e) j
      (by simpa only [nativeStreamingEdgeChildVertex_depth] using hj) l hl]

theorem nativeStreamingPatternFutureIntegral_edge_child_endpoint
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) :
    nativeStreamingPatternFutureIntegral D μ a q T F (.edge e (q e.depth)) =
      nativeStreamingPatternFutureIntegral D μ a q T F
        (.vertex (nativeStreamingEdgeChildVertex e)) := by
  classical
  unfold nativeStreamingPatternFutureIntegral
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
  simp only [nativeStreamingOriginLevel, nativeStreamingEdgeChildVertex_depth]
  by_cases hf : q e.depth < l
  · have hje : j < e.depth := by
      by_contra hh
      have hle := hq (show e.depth ≤ j by omega)
      exact (not_lt_of_ge (hl.2.trans hle)) hf
    simp only [hf, ite_true]
    exact nativeStreamingPatternMoment_future_edge_child_endpoint D μ a q hq hzero
      T F e j hje l ⟨hl.1.le, hl.2⟩
  · simp only [hf, ite_false]

end QuantitativeFollowup
