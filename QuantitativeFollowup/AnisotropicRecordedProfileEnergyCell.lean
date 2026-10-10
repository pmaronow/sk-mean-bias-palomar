module
public import QuantitativeFollowup.AnisotropicRecordedProfileFiniteCell
public import FourPapersCommon.FiniteStateCascadeGibbsTransport

@[expose] public section

/-! The physical parameter continuation transports to the actual complete
finite-state energy field, with its normalized Gaussian law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def anisotropicObservationEnergy (D : AnisotropicSpinModel n)
    (z : AnisotropicObservationState n) : FiniteStateField (Configuration n) :=
  anisotropicEnergyMap D (anisotropicObservationParameter D z)

theorem measurable_anisotropicObservationEnergy (D : AnisotropicSpinModel n) :
    Measurable (anisotropicObservationEnergy D) :=
  (anisotropicEnergyMap D).measurable.comp (measurable_anisotropicObservationParameter D)

theorem anisotropicFiniteTransition_energy_map (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (P : AnisotropicParameter n) :
    (anisotropicFiniteTransition D s i P).map (anisotropicEnergyMap D)=
      finiteStateGaussianCascadeKernel (anisotropicSchemeMass s)
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))
        (gtStateLogPartition (fun _ : Configuration n=>0)) (k+1-i) (anisotropicEnergyMap D P) := by
  let F:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) (k+1-i)
  have hFm : Measurable F :=
    (contDiff_one_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) _ (k+1-i)).continuous.measurable
  rw [anisotropicFiniteTransition,finiteStateGaussianStepKernel_apply _ _ _
    (contDiff_one_anisotropicFinitePotential D s _).continuous.measurable]
  change (finiteStateGaussianStepLaw (anisotropicSchemeMass s (k+1-i))
    (anisotropicSchemeInput D s (k+1-i)) (fun y=>F (anisotropicEnergyMap D y)) P).map
      (anisotropicEnergyMap D)=_
  rw [finiteStateGaussianStepLaw_comp_linear (anisotropicEnergyMap D) _ _ F hFm P]
  exact (finiteStateGaussianStepKernel_apply _ _ _ hFm _).symm

theorem anisotropicObservationTransition_scheme_energy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+1) :
    (anisotropicObservationTransition D (Paper.parisiSchemeMeasure s)
      (anisotropicFiniteMeshNode s i) (anisotropicFiniteMeshNode s (i+1))).map
        (anisotropicObservationEnergy D)=
      (finiteStateGaussianCascadeKernel (anisotropicSchemeMass s)
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))
        (gtStateLogPartition (fun _ : Configuration n=>0)) (k+1-i)).comap
          (anisotropicObservationEnergy D) (measurable_anisotropicObservationEnergy D) := by
  ext z A hA
  rw [Kernel.map_apply _ (measurable_anisotropicObservationEnergy D),Kernel.comap_apply]
  have hm : Measurable (anisotropicObservationParameter D):=measurable_anisotropicObservationParameter D
  have he:=congrArg (fun P : Measure (AnisotropicParameter n)=>P.map (anisotropicEnergyMap D))
    (anisotropicObservationTransition_scheme_parameter D s i hi z)
  rw [Measure.map_map (anisotropicEnergyMap D).measurable hm,
    anisotropicFiniteTransition_energy_map] at he
  exact congrArg (fun P : Measure (FiniteStateField (Configuration n))=>P A) he

end QuantitativeFollowup
