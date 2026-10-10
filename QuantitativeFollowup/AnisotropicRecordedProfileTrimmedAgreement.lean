module
public import QuantitativeFollowup.AnisotropicRecordedProfileFiniteTree
public import QuantitativeFollowup.FollowupCavityRootCharges

@[expose] public section

/-! Removing the actual zero-width initial observation gives precisely the
trimmed physical recorded law used by the finite streaming formulas. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem anisotropicRecordedProfileTreeLaw_scheme_trimmed_energy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) :
    (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T).map
        (fun z=>(anisotropicObservationEnergy D z.1,
          trimRecords T (observationTreeMap (anisotropicObservationEnergy D) T z.2)))=
      anisotropicTrimmedRecordedTreeLaw D s a T := by
  have hz : (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s (k+1))=0 := by
    rw [anisotropicSchemeInput_root_zero D s hq]
    ext x σ
    simp
  have ht:=finiteCascadeTreeGaussianJointLaw_trimRoot (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) a T hz
    (anisotropicRootEnergyMap D) 0
  have he:=congrArg (fun P : Measure (FiniteStateField (Configuration n)×
      Records (FiniteStateField (Configuration n)) (Configuration n) T)=>
        P.map (Prod.map id (trimRecords T)))
    (anisotropicRecordedProfileTreeLaw_scheme_energy D s a T)
  rw [Measure.map_map (measurable_id.prodMap (measurable_trimRecords T))
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T))] at he
  exact he.trans ht

end QuantitativeFollowup
