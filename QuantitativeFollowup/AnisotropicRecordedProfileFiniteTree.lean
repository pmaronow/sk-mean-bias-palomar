module
public import QuantitativeFollowup.AnisotropicRecordedProfileEnergyCell
public import QuantitativeFollowup.FollowupCavityRecordedDensity
public import FourPapersCommon.FiniteObservationTreeTransport

@[expose] public section

/-! Literal finite-scheme agreement of the actual arbitrary-profile recorded
genealogy. The map retains every complete energy field and every terminal
spin, including all conditionally independent branches. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable {n k : ℕ}

def anisotropicRecordedSchemeSchedule (s : RSBScheme k) (j : ℕ) : Paper.Overlap :=
  anisotropicFiniteMeshNode s (k+2-j)

theorem anisotropicRecordedProfileTreeKernel_scheme_energy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2) :
    (anisotropicRecordedProfileTreeKernel D (Paper.parisiSchemeMeasure s)
      (anisotropicRecordedSchemeSchedule s) T).map (observationTreeMap (anisotropicObservationEnergy D) T)=
      (finiteCascadeTreeRecordKernel (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) T).comap
          (anisotropicObservationEnergy D) (measurable_anisotropicObservationEnergy D) := by
  let κ:=fun l=>anisotropicObservationTransition D (Paper.parisiSchemeMeasure s)
    (anisotropicRecordedSchemeSchedule s (l+1)) (anisotropicRecordedSchemeSchedule s l)
  let η:=finiteStateGaussianCascadeKernel (anisotropicSchemeMass s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))
    (gtStateLogPartition (fun _ : Configuration n=>0))
  let θ:=(anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
    (measurable_anisotropicObservationParameter D)
  let ζ:=finiteStateGibbsKernel (fun _ : Configuration n=>0)
  have hκ : ∀l,IsMarkovKernel (κ l):=fun _=>inferInstance
  have hη : ∀l,IsMarkovKernel (η l):=fun l=>
    isMarkovKernel_finiteStateGaussianTerminalCascadeKernel _ _ (anisotropicSchemeMass_nonneg s) _ l
  haveI : IsMarkovKernel θ:=by unfold θ;infer_instance
  haveI : IsMarkovKernel ζ:=isMarkovKernel_finiteStateGibbsKernel _
  have hedge (l : ℕ) (hl : l<j) : (κ l).map (anisotropicObservationEnergy D)=
      (η l).comap (anisotropicObservationEnergy D) (measurable_anisotropicObservationEnergy D) := by
    have hlk : l≤k+1:=by omega
    have he:=anisotropicObservationTransition_scheme_energy D s (k+1-l) (by omega)
    rw [show k+1-l+1=k+2-l from by omega,
      show k+1-(k+1-l)=l from by omega] at he
    change (anisotropicObservationTransition D (Paper.parisiSchemeMeasure s)
      (anisotropicFiniteMeshNode s (k+2-(l+1))) (anisotropicFiniteMeshNode s (k+2-l))).map _=_
    simpa only [show k+2-(l+1)=k+1-l from by omega] using he
  have hleaf : θ=ζ.comap (anisotropicObservationEnergy D) (measurable_anisotropicObservationEnergy D) := by
    ext z A hA
    rfl
  have he:=observationTreeKernel_map κ hκ η hη θ ζ (anisotropicObservationEnergy D)
    (measurable_anisotropicObservationEnergy D) T hedge hleaf
  have hleft : observationTreeKernel κ θ T=anisotropicRecordedProfileTreeKernel D
      (Paper.parisiSchemeMeasure s) (anisotropicRecordedSchemeSchedule s) T := by
    clear he hedge hj
    induction T with
    | leaf => rfl
    | advance T ih => exact congrArg (fun K=>(Kernel.id ×ₖ K) ∘ₖ κ _) ih
    | fork T U ihT ihU => exact congrArg₂ (fun K L=>K ×ₖ L) ihT ihU
  have hright : observationTreeKernel η ζ T=finiteCascadeTreeRecordKernel
      (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) T := by
    clear hleft he hedge hj
    induction T with
    | leaf => rfl
    | advance T ih => exact congrArg (fun K=>(Kernel.id ×ₖ K) ∘ₖ η _) ih
    | fork T U ihT ihU => exact congrArg₂ (fun K L=>K ×ₖ L) ihT ihU
  rw [hleft,hright] at he
  exact he

theorem anisotropicObservationInitialLaw_scheme_energy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    (anisotropicObservationInitialLaw D (Paper.parisiSchemeMeasure s) a).map
      (anisotropicObservationEnergy D)=
      (anisotropicFiniteInitialLaw D s a).map (anisotropicEnergyMap D) := by
  rw [anisotropicObservationInitialLaw,anisotropicMeasureOuterLaw_scheme_eq_finite,
    Measure.map_map (measurable_anisotropicObservationEnergy D)
      (show Measurable (fun g : AnisotropicDisorder n=>(g,(0:Field n))) from measurable_id.prodMk measurable_const),
    anisotropicFiniteInitialLaw,Measure.map_map (anisotropicEnergyMap D).measurable
      (anisotropicDisorderInjection n).measurable]
  congr 1
  funext g
  simp only [Function.comp_def,anisotropicObservationEnergy,anisotropicObservationParameter,map_zero,add_zero]

theorem anisotropicRecordedProfileTreeLaw_scheme_energy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) :
    (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T).map
        (Prod.map (anisotropicObservationEnergy D) (observationTreeMap (anisotropicObservationEnergy D) T))=
      anisotropicFiniteRecordedTreeLaw D s a T := by
  haveI:=isMarkovKernel_finiteCascadeTreeRecordKernel (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) T
  rw [anisotropicRecordedProfileTreeLaw,observationJointLaw_map T _ _ _
    (anisotropicObservationEnergy D) (measurable_anisotropicObservationEnergy D)
    (anisotropicRecordedProfileTreeKernel_scheme_energy D s T le_rfl),
    anisotropicObservationInitialLaw_scheme_energy,anisotropicFiniteInitialLaw_energy]
  rfl

end QuantitativeFollowup
