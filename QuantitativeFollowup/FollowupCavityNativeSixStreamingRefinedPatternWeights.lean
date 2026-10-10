module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedDiscreteChargeGrouping
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedVertexPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexCoherence
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternEdgeEndpoint

@[expose] public section

/-! Actual original/fresh and CDF-weighted current attachments under
observation refinement. All callback equalities follow from marked laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem refined_weight_coarse_antitone (t : RSBScheme k)
    (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i,anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i) : Antitone q := by
  intro i j hij
  rw [←hlevels i,←hlevels j]
  exact anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme t)
    ((observationRefinementDepth_strictMono d).monotone hij)

private theorem refined_weight_coarse_zero (t : RSBScheme k)
    (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i,anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i) : q 0=1 := by
  rw [←hlevels 0]
  exact nativeStreamingSchemeSchedule_zero (cdfMassScheme t)

theorem nativeStreamingRefinedOriginalFreshWeight_agreement
    (D : AnisotropicSpinModel (n+1)) (t : RSBScheme k)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i,anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J≤k+1)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (i : ObservationLeaf T) :
    let s := cdfMassScheme t
    let μ := Paper.parisiSchemeMeasure s
    let Q := anisotropicRecordedSchemeSchedule s
    nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a (observationRefineTree d T)
      (fun v=>nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
        (nativeStreamingRefinedTerminalTest d T F)
        (.originalFresh (observationRefinementLeafEmbed d T i) (.vertex v))) =
      nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>nativeStreamingPatternMoment D μ a q T F (.originalFresh i o)) := by
  dsimp only
  have hQ := anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme t)
  have hq := refined_weight_coarse_antitone t q d hlevels
  have hzero := refined_weight_coarse_zero t q d hlevels
  refine nativeStreamingNormalizedRefinedChargeSum_eq_originWeightIntegral t a ha hfloor q d
    hlevels T hdepth a _ _ ?_ ?_ ?_ ?_
  · exact nativeStreamingPatternMoment_originalFresh_vertex_root_coherent D _ a _ _ _ _
  · intro v
    exact nativeStreamingPatternMoment_originalFresh_vertex_refinement D _ a q _ d hQ
      hlevels hzero T F i v
  · intro e p hp
    exact nativeStreamingPatternMoment_originalFresh_selected_refinement D _ a q _ d hQ
      hlevels hzero T F i e p hp
  · intro e
    exact nativeStreamingPatternMoment_originalFresh_edge_upper D _ a q hq hzero T F i e

theorem nativeStreamingRefinedOriginalFreshTerm_agreement
    (D : AnisotropicSpinModel (n+1)) (t : RSBScheme k)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i,anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J≤k+1)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    let s := cdfMassScheme t
    let μ := Paper.parisiSchemeMeasure s
    let Q := anisotropicRecordedSchemeSchedule s
    (-2:ℝ)*(∑i : ObservationLeaf (observationRefineTree d T),
      nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a (observationRefineTree d T)
        (fun v=>nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
          (nativeStreamingRefinedTerminalTest d T F) (.originalFresh i (.vertex v)))) =
      nativeStreamingSourceOriginalFreshTerm D μ a q T F := by
  classical
  dsimp only
  unfold nativeStreamingSourceOriginalFreshTerm
  congr 1
  symm
  apply Fintype.sum_equiv (nativeStreamingRefinementLeafEquiv d T)
  intro i
  exact (nativeStreamingRefinedOriginalFreshWeight_agreement D t a ha hfloor q d hlevels
    T hdepth F i).symm

theorem nativeStreamingRefinedCurrentWeight_agreement
    (D : AnisotropicSpinModel (n+1)) (t : RSBScheme k)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i,anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J≤k+1)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    let s := cdfMassScheme t
    let μ := Paper.parisiSchemeMeasure s
    let Q := anisotropicRecordedSchemeSchedule s
    nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a (observationRefineTree d T)
      (fun v=>Paper.parisiCDF μ (Q v.depth)*
        nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
          (nativeStreamingRefinedTerminalTest d T F) (.current (.vertex v))) =
      nativeStreamingSourceCurrentTerm D μ a q T F := by
  dsimp only
  unfold nativeStreamingSourceCurrentTerm
  have hQ := anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme t)
  have hq := refined_weight_coarse_antitone t q d hlevels
  have hzero := refined_weight_coarse_zero t q d hlevels
  refine nativeStreamingNormalizedRefinedChargeSum_eq_originWeightIntegral t a ha hfloor q d
    hlevels T hdepth a _ _ ?_ ?_ ?_ ?_
  · exact nativeStreamingPatternMoment_current_vertex_root_coherent D _ a _ _ _
  · intro v
    simp only [nativeStreamingRefinementVertexEmbed_depth,hlevels,nativeStreamingOriginLevel]
    rw [nativeStreamingPatternMoment_current_vertex_refinement D _ a q _ d hQ hlevels hzero T F v]
  · intro e p hp
    simp only [nativeStreamingEdgeSelectedVertex_depth d e p hp,nativeStreamingOriginLevel]
    congr 1
    simpa only [nativeStreamingRefinedTerminalTest] using
      nativeStreamingPatternMoment_current_selected_refinement D
        (Paper.parisiSchemeMeasure (cdfMassScheme t)) a q _ d hQ hlevels hzero T F e p hp
  · intro e
    simp only [nativeStreamingOriginLevel,nativeStreamingEdgeChildVertex_depth]
    rw [nativeStreamingPatternMoment_current_edge_upper D _ a q hq hzero T F e]

end QuantitativeFollowup
