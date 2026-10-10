module
public import QuantitativeFollowup.AnisotropicObservationSchemeEmbedding
public import QuantitativeFollowup.AnisotropicRecordedObservationRefinement
public import FourPapersCommon.FiniteObservationRefinementTransport

@[expose] public section

/-! Complete retained genealogical laws on exact prescribed observation
times are pushforwards of honest same-measure finite recorded-tree laws.
No finite-law identification is supplied as an assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k J : ℕ}

theorem anisotropicRecordedProfileTreeLaw_depthCast (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) {j l : ℕ}
    (h : j=l) (T : FiniteTerminalGenealogy j) :
    (anisotropicRecordedProfileTreeLaw D μ a q (observationTreeDepthCast h T)).map
      (Prod.map id (observationRecordDepthCast h T))=anisotropicRecordedProfileTreeLaw D μ a q T := by
  subst l
  change (anisotropicRecordedProfileTreeLaw D μ a q T).map id=_
  exact Measure.map_id

theorem anisotropicRecordedProfileTreeLaw_refined_scheme (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hlevels : ∀j,anisotropicRecordedSchemeSchedule s (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J=k+2) :
    (anisotropicFiniteRecordedTreeLaw D s a
      (observationTreeDepthCast hdepth (observationRefineTree d T))).map
        (Prod.map id (observationRefinementDepthProject (S:=Configuration n) d T hdepth))=
      (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a q T).map
        (Prod.map (anisotropicObservationEnergy D) (observationTreeMap (anisotropicObservationEnergy D) T)) := by
  let U : FiniteTerminalGenealogy (k+2):=observationTreeDepthCast hdepth (observationRefineTree d T)
  let φ : AnisotropicObservationState n→FiniteStateField (Configuration n):=anisotropicObservationEnergy D
  have hφ : Measurable φ:=measurable_anisotropicObservationEnergy D
  have hmap:=anisotropicRecordedProfileTreeLaw_scheme_energy D s a U
  have hp : Measurable (observationRefinementDepthProject
      (E:=FiniteStateField (Configuration n)) (S:=Configuration n) d T hdepth):=
    measurable_observationRefinementDepthProject (S:=Configuration n) d T hdepth
  have hm :=measurable_observationTreeMap (E:=AnisotropicObservationState n) (F:=FiniteStateField (Configuration n)) (S:=Configuration n) (j:=k+2) φ hφ U
  have hc : (Prod.map id (observationRefinementDepthProject (S:=Configuration n) d T hdepth)) ∘
      Prod.map φ (observationTreeMap (S:=Configuration n) φ U)=
      Prod.map φ (observationTreeMap (S:=Configuration n) φ T) ∘
        (Prod.map id (observationRefinementProject (S:=Configuration n) d T)) ∘
          Prod.map id (observationRecordDepthCast (S:=Configuration n) hdepth (observationRefineTree d T)) := by
    rw [Prod.map_comp_map,Prod.map_comp_map,Prod.map_comp_map]
    congr 1
    exact (observationRefinementDepthProject_map (S:=Configuration n) φ d T hdepth).symm
  rw [←hmap,Measure.map_map (measurable_id.prodMap hp) (hφ.prodMap hm),hc,
    ←Measure.map_map (hφ.prodMap (measurable_observationTreeMap (S:=Configuration n) φ hφ T))
      ((measurable_id.prodMap (measurable_observationRefinementProject (S:=Configuration n) d T)).comp
        (measurable_id.prodMap (measurable_observationRecordDepthCast (S:=Configuration n) hdepth _))),
    ←Measure.map_map (measurable_id.prodMap (measurable_observationRefinementProject (S:=Configuration n) d T))
      (measurable_id.prodMap (measurable_observationRecordDepthCast (S:=Configuration n) hdepth _)),
    anisotropicRecordedProfileTreeLaw_depthCast,
    anisotropicRecordedProfileTreeLaw_refinement D (Paper.parisiSchemeMeasure s) a q
      (anisotropicRecordedSchemeSchedule s) d (anisotropicRecordedSchemeSchedule_antitone s) hlevels]

/-- The finite law can be chosen concretely for every finite profile and
finite complete observation schedule. Original observations, including
repeated ones, are retained exactly. -/
theorem exists_anisotropic_finite_recorded_observation_adapter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (hs : s.q 1=0) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (J : ℕ) (hJ : 0<J) (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J) :
    ∃(K : ℕ)(r : RSBScheme K)(d : ℕ→ℕ)(hdepth : observationRefinementDepth d J=K+2),
      Paper.parisiSchemeMeasure r=Paper.parisiSchemeMeasure s ∧ r.q 1=0 ∧
      (anisotropicFiniteRecordedTreeLaw D r a
        (observationTreeDepthCast hdepth (observationRefineTree d T))).map
          (Prod.map id (observationRefinementDepthProject (S:=Configuration n) d T hdepth))=
        (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a q T).map
          (Prod.map (anisotropicObservationEnergy D) (observationTreeMap (anisotropicObservationEnergy D) T)) := by
  obtain ⟨K,r,e,hr,hrzero,he,hezero,hetop,hlevels⟩:=
    exists_same_measure_observation_scheme_embedding s hs q hq J hJ hzero htop
  let d:=observationEmbeddingGaps e
  have hdepth : observationRefinementDepth d J=K+2:=
    (observationRefinementDepth_embedding e he hezero J).trans hetop
  refine ⟨K,r,d,hdepth,hr,hrzero,?_⟩
  have hl (j : ℕ) : anisotropicRecordedSchemeSchedule r (observationRefinementDepth d j)=q j := by
    rw [observationRefinementDepth_embedding e he hezero]
    exact hlevels j
  rw [←hr]
  exact anisotropicRecordedProfileTreeLaw_refined_scheme D r a q d hl T hdepth

end QuantitativeFollowup
