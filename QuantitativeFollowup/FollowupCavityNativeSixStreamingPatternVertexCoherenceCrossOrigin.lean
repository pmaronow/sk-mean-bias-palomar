module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexCoherenceCross
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternCrossEdgeEndpoint

@[expose] public section

/-! A fixed edge origin retains its true inserted ancestor and the whole
original record. Its actual conditional fresh-spin product makes each
old-vertex cross callback coherent at fork roots. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem crossOrigin_terminalMoment_edge_vertex_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (r : Paper.Overlap) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    let d := nativeStreamingEdgeSubdivision e.depth
    let Q := nativeStreamingEdgeSchedule q e.depth r
    let R := observationRefineTree d T
    let w := nativeStreamingEdgeRefinedVertex d e
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgeVertexPairProbability D μ a q T e v r) G =
      ∫z, ∫s, G (finiteCascadeRecordTerminalSpins T (observationRefinementProject d T z.2),s)
        ∂((((anisotropicRecordedProfileTreeKernel D μ Q (observationLinearTree w.depth)).map
          (observationLinearSpin w.depth)) (nativeStreamingVertexState w z.1 z.2)).prod
          (((anisotropicRecordedProfileTreeKernel D μ Q
            (observationLinearTree (observationRefinementDepth d v.depth))).map
              (observationLinearSpin (observationRefinementDepth d v.depth)))
            (nativeStreamingVertexState v z.1 (observationRefinementProject d T z.2))))
        ∂anisotropicRecordedProfileTreeLaw D μ a Q R := by
  classical
  dsimp only
  let d : ℕ → ℕ := nativeStreamingEdgeSubdivision e.depth
  let Q : ℕ → Paper.Overlap := nativeStreamingEdgeSchedule q e.depth r
  let w := nativeStreamingEdgeRefinedVertex d e
  let V := nativeStreamingRefinementVertexEmbed d T v
  let P := nativeStreamingCrossVertexProbability D μ a Q (observationRefineTree d T) w V
  let f : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n)) → ℝ := fun z =>
    G (finiteCascadeRecordTerminalSpins T (observationRefinementProject d T z.1.2),z.2)
  have hc : Continuous f :=
    (continuous_of_discreteTopology (f := G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp
        ((continuous_observationRefinementProject d T).comp continuous_fst.snd)).prodMk
          continuous_snd)
  have hi : Integrable f (P : Measure _) := by
    apply (integrable_const (nativeStreamingTerminalMarkBound T G)).mono' hc.aestronglyMeasurable
    exact .of_forall fun z =>
      Finset.single_le_sum (fun σ _ => norm_nonneg (G σ)) (Finset.mem_univ _)
  have hl := nativeStreamingCrossVertexProbability_eq_actual_continuations D μ a Q (observationRefineTree d T) w V
  rw [hl] at hi
  haveI := nativeStreamingActualContinuationKernel_markov D μ Q observationLinearTree
    observationLinearSpin (fun j => measurable_observationLinearSpin j) (observationRefineTree d T) w
  haveI := nativeStreamingActualContinuationKernel_markov D μ Q observationLinearTree
    observationLinearSpin (fun j => measurable_observationLinearSpin j) (observationRefineTree d T) V
  have hm : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n)) =>
      ((z.1.1,observationRefinementProject d T z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk
      ((measurable_observationRefinementProject d T).comp measurable_fst.snd)).prodMk
        measurable_snd
  have hcG : Continuous (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f := G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk
        continuous_snd)
  unfold nativeStreamingTerminalMarkMoment nativeStreamingEdgeVertexPairProbability
  rw [ProbabilityMeasure.toMeasure_map,integral_map hm.aemeasurable hcG.aestronglyMeasurable]
  change (∫z, f z ∂(P : Measure _)) = _
  rw [hl,Measure.integral_compProd hi]
  simp only [Kernel.prod_apply,nativeStreamingActualContinuationKernel,Kernel.comap_apply,
    Function.uncurry_def,V,f,
    nativeStreamingRefinementVertexEmbed_state]
  rw [nativeStreamingRefinementVertexEmbed_depth d T v]

private theorem crossOrigin_terminalMoment_fresh_swap
    (T : FiniteTerminalGenealogy J)
    (P : ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)))
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    nativeStreamingTerminalMarkMoment (P.map (fun z => (z.1,(z.2.2,z.2.1)))) G =
      nativeStreamingTerminalMarkMoment P (fun z => G (z.1,(z.2.2,z.2.1))) := by
  have hm : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)) => (z.1,(z.2.2,z.2.1))) :=
    measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst)
  have hc : Continuous (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f := G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk
        continuous_snd)
  unfold nativeStreamingTerminalMarkMoment
  rw [ProbabilityMeasure.toMeasure_map,integral_map hm.aemeasurable hc.aestronglyMeasurable]
private theorem crossOrigin_edge_vertex_test_root_coherent
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (r : Paper.Overlap)
    (G : ℕ → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    nativeStreamingRootCoherent T (fun v =>
      nativeStreamingTerminalMarkMoment (nativeStreamingEdgeVertexPairProbability D μ a q T e v r)
        (G (finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)))) := by
  let d : ℕ → ℕ := nativeStreamingEdgeSubdivision e.depth
  let Q : ℕ → Paper.Overlap := nativeStreamingEdgeSchedule q e.depth r
  let w := nativeStreamingEdgeRefinedVertex d e
  have h := nativeStreamingRootCoherent_integral
    (A := AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T))
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T)) T
    (fun (z : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) v =>
      ∫s, G (finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e))
      (finiteCascadeRecordTerminalSpins T (observationRefinementProject d T z.2),s)
      ∂((((anisotropicRecordedProfileTreeKernel D μ Q (observationLinearTree w.depth)).map
        (observationLinearSpin w.depth)) (nativeStreamingVertexState w z.1 z.2)).prod
        (((anisotropicRecordedProfileTreeKernel D μ Q
          (observationLinearTree (observationRefinementDepth d v.depth))).map
            (observationLinearSpin (observationRefinementDepth d v.depth)))
          (nativeStreamingVertexState v z.1 (observationRefinementProject d T z.2)))))
    (fun z => nativeStreamingVertexStateCommonPath_root_coherent
      (fun j c x => ∫s, G c
        (finiteCascadeRecordTerminalSpins T (observationRefinementProject d T z.2),s)
        ∂((((anisotropicRecordedProfileTreeKernel D μ Q (observationLinearTree w.depth)).map
          (observationLinearSpin w.depth)) (nativeStreamingVertexState w z.1 z.2)).prod
          (((anisotropicRecordedProfileTreeKernel D μ Q
            (observationLinearTree (observationRefinementDepth d j))).map
              (observationLinearSpin (observationRefinementDepth d j))) x)))
      T (nativeStreamingEdgeChildVertex e) z.1 (observationRefinementProject d T z.2))
  convert h using 1
  funext v
  exact crossOrigin_terminalMoment_edge_vertex_integral D μ a q T e r v _

theorem nativeStreamingPatternMoment_cross_left_origin_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (o : NativeStreamingOrigin T) :
    nativeStreamingRootCoherent T (fun v =>
      nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) o)) := by
  cases o with
  | vertex w => exact nativeStreamingPatternMoment_cross_left_vertex_root_coherent D μ a q T F w
  | edge e r =>
      have h := crossOrigin_edge_vertex_test_root_coherent D μ a q T e r
        (fun c z => nativeStreamingDefectSpinTest T F
          (nativeStreamingOldSelectedCommonClock c e.depth r (q c)) (z.1,(z.2.2,z.2.1)))
      convert h using 1
      funext v
      simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,
        nativeStreamingOriginCommonClock]
      exact crossOrigin_terminalMoment_fresh_swap T _ _

theorem nativeStreamingPatternMoment_cross_right_origin_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (o : NativeStreamingOrigin T) :
    nativeStreamingRootCoherent T (fun v =>
      nativeStreamingPatternMoment D μ a q T F (.cross o (.vertex v))) := by
  cases o with
  | vertex w => exact nativeStreamingPatternMoment_cross_right_vertex_root_coherent D μ a q T F w
  | edge e r =>
      exact crossOrigin_edge_vertex_test_root_coherent D μ a q T e r
        (fun c => nativeStreamingDefectSpinTest T F
          (nativeStreamingOldSelectedCommonClock c e.depth r (q c)))

end QuantitativeFollowup
