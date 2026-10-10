module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternEdgeEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexEndpoint

@[expose] public section

/-! At an edge's retained child endpoint, both cross-pattern spin orders
have the genuine old-vertex product law and the original common clock. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

private theorem endpoint_defect_spin_swap (q : ℝ) (σ τ : Configuration (n+1)) :
    cavitySpinOverlapDefect n q σ τ = cavitySpinOverlapDefect n q τ σ := by
  unfold cavitySpinOverlapDefect
  have hs : (∑ i : Fin n, anisotropicCouplingFeature (cavityIncidentEdge i) σ *
      anisotropicCouplingFeature (cavityIncidentEdge i) τ) =
      ∑ i : Fin n, anisotropicCouplingFeature (cavityIncidentEdge i) τ *
        anisotropicCouplingFeature (cavityIncidentEdge i) σ := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hs]
  ring

private theorem endpoint_terminal_defect_fresh_swap
    (T : FiniteTerminalGenealogy J)
    (P : ProbabilityMeasure ((AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
        (Configuration (n+1) × Configuration (n+1))))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (q : Paper.Overlap) :
    nativeStreamingTerminalMarkMoment (P.map (fun z => (z.1,(z.2.2,z.2.1))))
      (nativeStreamingDefectSpinTest T F q) =
      nativeStreamingTerminalMarkMoment P (nativeStreamingDefectSpinTest T F q) := by
  let X := ((AnisotropicObservationState (n+1) ×
    Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
      (Configuration (n+1) × Configuration (n+1)))
  have hm : Measurable (fun z : X => (z.1,(z.2.2,z.2.1))) :=
    measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst)
  have hc : Continuous (fun z : X => nativeStreamingDefectSpinTest T F q
      (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f := nativeStreamingDefectSpinTest T F q)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk continuous_snd)
  unfold nativeStreamingTerminalMarkMoment
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z => by
    simp only [nativeStreamingDefectSpinTest]
    rw [endpoint_defect_spin_swap]

private theorem endpoint_cross_vertex_probability_fresh_swap
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexProbability D μ a q T v w).map
      (fun z => (z.1,(z.2.2,z.2.1))) =
        nativeStreamingCrossVertexProbability D μ a q T w v := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero T v w,
    nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero T w v]
  change (nativeStreamingCrossVertexLaw D μ a q T v w).map (Prod.map id Prod.swap) =
    nativeStreamingCrossVertexLaw D μ a q T w v
  unfold nativeStreamingCrossVertexLaw nativeStreamingCrossVertexKernel
  rw [←Measure.compProd_map measurable_swap,Kernel.map_prod_swap]

private theorem endpoint_cross_vertex_moment_symm
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v w : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.vertex w)) =
      nativeStreamingPatternMoment D μ a q T F (.cross (.vertex w) (.vertex v)) := by
  have hp := endpoint_cross_vertex_probability_fresh_swap D μ a q hq hzero T v w
  have H := endpoint_terminal_defect_fresh_swap T
    (nativeStreamingCrossVertexProbability D μ a q T v w) F
      (q (finiteCascadeCommonPathDepth T v w))
  rw [hp] at H
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,
    nativeStreamingOriginCommonClock]
  rw [←nativeStreamingSelectedGeometry_commonPathDepth_symm T v w]
  exact H.symm

private theorem endpoint_origin_common_clock_edge_child
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingOriginCommonClock q T (.edge e (q e.depth)) (.vertex v) =
      nativeStreamingOriginCommonClock q T (.vertex (nativeStreamingEdgeChildVertex e)) (.vertex v) := by
  calc
    _ = nativeStreamingOriginCommonClock q T (.vertex v) (.edge e (q e.depth)) := rfl
    _ = nativeStreamingOriginCommonClock q T (.vertex v)
        (.vertex (nativeStreamingEdgeChildVertex e)) :=
      nativeStreamingOriginCommonClock_edge_upper_vertex q T v e
    _ = _ := congrArg q (nativeStreamingSelectedGeometry_commonPathDepth_symm T v
      (nativeStreamingEdgeChildVertex e))

theorem nativeStreamingPatternMoment_cross_edge_child_endpoint
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.edge e (q e.depth)) (.vertex v)) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeChildVertex e)) (.vertex v)) := by
  have hp := nativeStreamingEdgeVertexPairProbability_endpoint D μ a q hq hzero T e v false
  simp only [nativeStreamingEndpointVertex,nativeStreamingEdgeChildVertex_depth] at hp
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability]
  rw [hp,endpoint_origin_common_clock_edge_child]

theorem nativeStreamingPatternMoment_cross_child_endpoint_edge
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.edge e (q e.depth))) =
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex v) (.vertex (nativeStreamingEdgeChildVertex e))) := by
  calc
    _ = nativeStreamingPatternMoment D μ a q T F (.cross (.edge e (q e.depth)) (.vertex v)) := by
      simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,
        nativeStreamingOriginCommonClock]
      exact endpoint_terminal_defect_fresh_swap T _ F _
    _ = nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex (nativeStreamingEdgeChildVertex e)) (.vertex v)) :=
      nativeStreamingPatternMoment_cross_edge_child_endpoint D μ a q hq hzero T F e v
    _ = _ := endpoint_cross_vertex_moment_symm D μ a q hq hzero T F
      (nativeStreamingEdgeChildVertex e) v

end QuantitativeFollowup
