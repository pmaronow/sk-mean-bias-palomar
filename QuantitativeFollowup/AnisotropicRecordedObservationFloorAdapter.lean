module
public import QuantitativeFollowup.AnisotropicRecordedObservationAdapter
public import FourPapersCommon.FiniteSchemeCDFMassNormalization

@[expose] public section

/-! Exact observation refinement retaining the genuine lower CDF floor.
The canonical right-CDF masses also handle atoms and repeated nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem exists_same_measure_floor_observation_scheme_embedding (s : RSBScheme k)
    (hs : s.q 1=0) (a : ℝ) (ha : a≤Paper.parisiCDF (Paper.parisiSchemeMeasure s) 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (J : ℕ) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) :
    ∃(K : ℕ)(r : RSBScheme K)(e : ℕ→ℕ),Paper.parisiSchemeMeasure r=Paper.parisiSchemeMeasure s ∧
      r.q 1=0 ∧ a≤r.m 1 ∧ StrictMono e ∧ e 0=0 ∧ e J=K+2 ∧
      ∀j,anisotropicRecordedSchemeSchedule r (e j)=q j := by
  obtain ⟨K,r,e,hr,hrzero,he,hezero,hetop,hlevels⟩:=
    exists_same_measure_observation_scheme_embedding s hs q hq J hJ hzero htop
  refine ⟨K,cdfMassScheme r,e,(parisiSchemeMeasure_cdfMassScheme r).trans hr,
    hrzero,?_,he,hezero,hetop,hlevels⟩
  apply cdfMassScheme_preserves_floor r hrzero
  simpa only [hr] using ha

theorem exists_anisotropic_finite_recorded_floor_observation_adapter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (hs : s.q 1=0) (a : ℝ)
    (ha : a≤Paper.parisiCDF (Paper.parisiSchemeMeasure s) 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (J : ℕ) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J) :
    ∃(K : ℕ)(r : RSBScheme K)(d : ℕ→ℕ)(hdepth : observationRefinementDepth d J=K+2),
      Paper.parisiSchemeMeasure r=Paper.parisiSchemeMeasure s ∧ r.q 1=0 ∧ a≤r.m 1 ∧
      (anisotropicFiniteRecordedTreeLaw D r a
        (observationTreeDepthCast hdepth (observationRefineTree d T))).map
          (Prod.map id (observationRefinementDepthProject (S:=Configuration n) d T hdepth))=
        (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a q T).map
          (Prod.map (anisotropicObservationEnergy D) (observationTreeMap (anisotropicObservationEnergy D) T)) := by
  obtain ⟨K,r,e,hr,hrzero,har,he,hezero,hetop,hlevels⟩:=
    exists_same_measure_floor_observation_scheme_embedding s hs a ha q hq J hJ hzero htop
  let d:=observationEmbeddingGaps e
  have hdepth : observationRefinementDepth d J=K+2:=
    (observationRefinementDepth_embedding e he hezero J).trans hetop
  refine ⟨K,r,d,hdepth,hr,hrzero,har,?_⟩
  have hl (j : ℕ) : anisotropicRecordedSchemeSchedule r (observationRefinementDepth d j)=q j := by
    rw [observationRefinementDepth_embedding e he hezero]
    exact hlevels j
  rw [←hr]
  exact anisotropicRecordedProfileTreeLaw_refined_scheme D r a q d hl T hdepth

end QuantitativeFollowup
