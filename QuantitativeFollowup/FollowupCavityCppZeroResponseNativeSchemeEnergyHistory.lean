module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeSchemeHistory
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterHistory
public import QuantitativeFollowup.AnisotropicRecordedProfileEnergyCell
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerProjection

@[expose] public section

/-! The true native marked history and the independent-coordinate outer
posterior have the same complete energy-history law for every finite scheme.
This law identity retains all nodes, their order, and the terminal spin. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavitySchemeEnergyHistoryProjection (D : AnisotropicSpinModel n) :
    FiniteHistory (AnisotropicParameter n) (k+2)→FiniteHistory (FiniteStateField (Configuration n)) (k+2) :=
  fun h i=>anisotropicEnergyMap D (h i)

theorem measurable_cavitySchemeEnergyHistoryProjection (D : AnisotropicSpinModel n) :
    Measurable (cavitySchemeEnergyHistoryProjection (k:=k) D) :=
  Measurable.of_eval fun i=>(anisotropicEnergyMap D).measurable.comp (measurable_pi_apply i)

theorem cavityFiniteJointLaw_energy_history (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    (anisotropicFiniteJointLaw D s a).map (Prod.map (cavitySchemeEnergyHistoryProjection D) id)=
      finiteHistoryLaw
        (cavityOuterHistoryInitial (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
          (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0)
        (cascadePosteriorKernel (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
          (cavityFiniteEnergyInput D s) (k+2)) (k+2) ⊗ₘ
        cascadePosteriorTerminalKernel (fun _ : Configuration n=>0) (k+2) :=by
  let η:=cascadePosteriorKernel (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) (k+2)
  have hη : ∀i,IsMarkovKernel (η i):=cascadePosteriorKernel_markov _ _ (anisotropicSchemeMass_nonneg s) _ _
  have hsection (i : ℕ) (P : AnisotropicParameter n) :
      (anisotropicFiniteTransition D s i P).map (anisotropicEnergyMap D)=η i (anisotropicEnergyMap D P) :=by
    have hL:(fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))=cavityFiniteEnergyInput D s:=rfl
    have he:=anisotropicFiniteTransition_energy_map D s i P
    rw [hL] at he
    simpa only [η,cascadePosteriorKernel,show k+2-1-i=k+1-i from by omega] using he
  have hh:=finiteHistoryLaw_map_states (anisotropicFiniteInitialLaw D s a)
    (anisotropicFiniteTransition D s) η (fun _=>inferInstance) hη
    (anisotropicEnergyMap D) (anisotropicEnergyMap D).measurable hsection (k+2)
  have ht (h : FiniteHistory (AnisotropicParameter n) (k+2)) :
      (anisotropicFiniteTerminalKernel D s h).map id=
        cascadePosteriorTerminalKernel (fun _ : Configuration n=>0) (k+2)
          (cavitySchemeEnergyHistoryProjection D h) :=by
    rw [Measure.map_id]
    change anisotropicFiniteSpinKernel D s 0 (h (Fin.last (k+2)))=_
    rw [anisotropicFiniteSpinKernel_zero_eq_terminalKernel]
    rfl
  rw [anisotropicFiniteJointLaw,map_compProd_map_pair _ _
    (cascadePosteriorTerminalKernel (fun _ : Configuration n=>0) (k+2))
    (cavitySchemeEnergyHistoryProjection D) id (measurable_cavitySchemeEnergyHistoryProjection D) measurable_id ht]
  change ((finiteHistoryLaw _ _ _).map
    (fun h : FiniteHistory (AnisotropicParameter n) (k+2)=>fun i=>anisotropicEnergyMap D (h i))) ⊗ₘ _=_
  rw [hh,anisotropicFiniteInitialLaw_energy,
    cavityOuterHistoryInitial_eq_tilted_field _ _ (anisotropicSchemeMass_nonneg s)]
  rfl

theorem cavityOuterPosteriorHistory_eq_native_scheme (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    (cavityOuterPosteriorLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0).map
        (cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2) (anisotropicRootEnergyMap D) 0)=
      (anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a).map
        (fun p=>(cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s p.1),p.2)) :=by
  rw [cavityOuterHistoryMap_law _ _ (anisotropicSchemeMass_nonneg s),
    ←cavityFiniteJointLaw_energy_history D s a,←cavityNativeSchemeMarkedHistory_law D s a,
    Measure.map_map ((measurable_cavitySchemeEnergyHistoryProjection D).prodMap measurable_id)
      ((measurable_cavityNativeSchemeHistory D s).prodMap measurable_id)]
  rfl

end QuantitativeFollowup
