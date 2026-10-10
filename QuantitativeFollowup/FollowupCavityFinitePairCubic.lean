module
public import QuantitativeFollowup.FollowupCavityGraftedCubicMoments
public import QuantitativeFollowup.AnisotropicRecordedProfileTrimmedAgreement
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! The native pair identification transports to the literal finite
Gaussian recorded law. It retains actual terminal spins and their common
physical level, including every repeated node and zero mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteRecorded_leafPair_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (i l : ObservationLeaf T) (hil : i≠l) :
    (anisotropicFiniteRecordedTreeLaw D s a T).map
      (fun z=>(observationLeafSpin T i z.2,observationLeafSpin T l z.2))=
      (anisotropicBinarySpinProbability D (Paper.parisiSchemeMeasure s) a
        (cavityProfileLevel s (observationCommonLevel T i l)) : Measure _) := by
  obtain ⟨hzero,hroot,hmono⟩:=cavityProfileLevel_clock s
  have hf : Measurable (fun z : FiniteStateField (Configuration n)×
      Records (FiniteStateField (Configuration n)) (Configuration n) T=>
      (observationLeafSpin T i z.2,observationLeafSpin T l z.2)):=
    ((measurable_observationLeafSpin T i).comp measurable_snd).prodMk
      ((measurable_observationLeafSpin T l).comp measurable_snd)
  rw [←anisotropicRecordedProfileTreeLaw_scheme_energy D s a T,
    Measure.map_map hf ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T))]
  have he : (fun z : AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T=>
      (observationLeafSpin T i (observationTreeMap (anisotropicObservationEnergy D) T z.2),
        observationLeafSpin T l (observationTreeMap (anisotropicObservationEnergy D) T z.2)))=
      fun z=>(observationLeafSpin T i z.2,observationLeafSpin T l z.2) := by
    funext z
    rw [observationLeafSpin_treeMap,observationLeafSpin_treeMap]
  change (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
    (cavityProfileLevel s) T).map
      (fun z => (observationLeafSpin T i
        (observationTreeMap (anisotropicObservationEnergy D) T z.2),
        observationLeafSpin T l
        (observationTreeMap (anisotropicObservationEnergy D) T z.2)))=_
  rw [he]
  exact anisotropicRecordedProfile_leafPair_law D (Paper.parisiSchemeMeasure s) a
    (cavityProfileLevel s) hzero T hroot hmono i l hil

theorem cavityFiniteRecorded_leafPair_cubic_eq (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (i l : ObservationLeaf T) (hil : i≠l) :
    (∫z,|cavityRestOverlap n (observationLeafSpin T i z.2)
      (observationLeafSpin T l z.2)-(cavityProfileLevel s (observationCommonLevel T i l):ℝ)|^3
        ∂anisotropicFiniteRecordedTreeLaw D s a T)=
      cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
        (cavityProfileLevel s (observationCommonLevel T i l)) := by
  let f : Configuration (n+1)×Configuration (n+1)→ℝ:=fun z=>
    |cavityRestOverlap n z.1 z.2-(cavityProfileLevel s (observationCommonLevel T i l):ℝ)|^3
  have hf : Measurable (fun z : FiniteStateField (Configuration (n+1))×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) T=>
      (observationLeafSpin T i z.2,observationLeafSpin T l z.2)):=
    ((measurable_observationLeafSpin T i).comp measurable_snd).prodMk
      ((measurable_observationLeafSpin T l).comp measurable_snd)
  have he:=integral_map (μ:=anisotropicFiniteRecordedTreeLaw D s a T)
    hf.aemeasurable (measurable_of_finite f).aestronglyMeasurable
  rw [cavityFiniteRecorded_leafPair_law D s a T i l hil] at he
  exact he.symm

end QuantitativeFollowup
