module
public import QuantitativeFollowup.AnisotropicVarianceRestartHistory
public import QuantitativeFollowup.AnisotropicFiniteFeatureKernels
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerProjection

@[expose] public section

/-! The genuine fixed-initial-field anisotropic restart, retaining every
chronological state and the terminal spin, is the normalized Gaussian
posterior after the actual energy embedding. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem restartFiniteTransition_energy_map (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (P : AnisotropicParameter n) :
    (anisotropicFiniteTransition D s i P).map (anisotropicEnergyMap D)=
      cascadePosteriorKernel (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) (k+2) i
          (anisotropicEnergyMap D P) := by
  let F:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) (k+1-i)
  have hc:=contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) (k+1-i)
  rw [anisotropicFiniteTransition,finiteStateGaussianStepKernel_apply _ _ _
    (contDiff_one_anisotropicFinitePotential D s _).continuous.measurable]
  rw [cascadePosteriorKernel,show k+2-1-i=k+1-i by omega,
    finiteStateGaussianCascadeKernel]
  change _=(finiteStateGaussianStepKernel _ _ F) _
  rw [finiteStateGaussianStepKernel_apply _ _ _ hc.continuous.measurable]
  exact finiteStateGaussianStepLaw_comp_linear (anisotropicEnergyMap D)
    (anisotropicSchemeInput D s (k+1-i)) (anisotropicSchemeMass s (k+1-i)) F hc.continuous.measurable P

def anisotropicFiniteRestartEnergyHistory (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (sample : VectorDisorderBrownianSample n) : FiniteHistory (FiniteStateField (Configuration n)) (k+2) :=
  fun i=>anisotropicEnergyMap D
    (anisotropicFiniteRestartPhysicalHistory D s g q x (k+2) sample i)

theorem measurable_anisotropicFiniteRestartEnergyHistory (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Measurable (anisotropicFiniteRestartEnergyHistory D s g q x) :=
  Measurable.of_eval fun i=>(anisotropicEnergyMap D).measurable.comp
    ((measurable_pi_apply i).comp (measurable_anisotropicFiniteRestartPhysicalHistory D s g q x _))

theorem anisotropicFiniteRestartEnergyHistory_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    (vectorDisorderBrownianMeasure n).map (anisotropicFiniteRestartEnergyHistory D s g q x)=
      cascadePosteriorHistoryLaw (fun _ : Configuration n=>0)
        (anisotropicSchemeMass (vectorClampedScheme s q q.property))
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
        (k+2) (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)) := by
  let cs:=vectorClampedScheme s q q.property
  have hT : Measurable (fun h : FiniteHistory (AnisotropicParameter n) (k+2)=>
      fun i=>anisotropicEnergyMap D (h i)) :=
    Measurable.of_eval fun i=>(anisotropicEnergyMap D).measurable.comp (measurable_pi_apply i)
  change (vectorDisorderBrownianMeasure n).map
    ((fun h : FiniteHistory (AnisotropicParameter n) (k+2)=>fun i=>anisotropicEnergyMap D (h i)) ∘
      anisotropicFiniteRestartPhysicalHistory D s g q x (k+2))=_
  rw [←Measure.map_map hT (measurable_anisotropicFiniteRestartPhysicalHistory D s g q x _),
    anisotropicFiniteRestartPhysical_history_law D s g q x (k+2) le_rfl]
  have hsection (i : ℕ) (P : AnisotropicParameter n) :
      (anisotropicFiniteRestartPhysicalKernel D s q i P).map (anisotropicEnergyMap D)=
        cascadePosteriorKernel (fun _ : Configuration n=>0) (anisotropicSchemeMass cs)
          (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l)) (k+2) i
            (anisotropicEnergyMap D P) := by
    simpa only [anisotropicFiniteRestartPhysicalKernel,cascadePosteriorKernel,
      show k+1+2-1-(i+1)=k+2-1-i by omega] using
      restartFiniteTransition_energy_map D cs (i+1) P
  rw [finiteHistoryLaw_map_states _ _ _ (fun _=>inferInstance)
    (cascadePosteriorKernel_markov _ _ (anisotropicSchemeMass_nonneg cs) _ _)
    (anisotropicEnergyMap D) (anisotropicEnergyMap D).measurable hsection (k+2),
    Measure.map_dirac' (anisotropicEnergyMap D).measurable]
  rfl

def anisotropicFiniteRestartSpinKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Kernel (VectorDisorderBrownianSample n) (Configuration n) :=
  (finiteStateGibbsKernel (fun _ : Configuration n=>0)).comap
    (fun sample=>anisotropicFiniteRestartEnergyHistory D s g q x sample (Fin.last (k+2)))
    ((measurable_pi_apply _).comp (measurable_anisotropicFiniteRestartEnergyHistory D s g q x))

instance anisotropicFiniteRestartSpinKernel_markov (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    IsMarkovKernel (anisotropicFiniteRestartSpinKernel D s g q x) := by
  haveI:=isMarkovKernel_finiteStateGibbsKernel (fun _ : Configuration n=>0)
  unfold anisotropicFiniteRestartSpinKernel
  infer_instance

def anisotropicFiniteRestartMarkedLaw (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Measure (VectorDisorderBrownianSample n×Configuration n) :=
  vectorDisorderBrownianMeasure n ⊗ₘ anisotropicFiniteRestartSpinKernel D s g q x

instance anisotropicFiniteRestartMarkedLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    IsProbabilityMeasure (anisotropicFiniteRestartMarkedLaw D s g q x) := by
  unfold anisotropicFiniteRestartMarkedLaw
  infer_instance

theorem anisotropicFiniteRestartMarkedLaw_posterior_map (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    (anisotropicFiniteRestartMarkedLaw D s g q x).map
      (Prod.map (anisotropicFiniteRestartEnergyHistory D s g q x) id)=
      cascadePosteriorLaw (fun _ : Configuration n=>0)
        (anisotropicSchemeMass (vectorClampedScheme s q q.property))
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
        (k+2) (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)) := by
  rw [anisotropicFiniteRestartMarkedLaw,map_compProd_map_pair
    (vectorDisorderBrownianMeasure n) (anisotropicFiniteRestartSpinKernel D s g q x)
    (cascadePosteriorTerminalKernel (fun _ : Configuration n=>0) (k+2))
    (anisotropicFiniteRestartEnergyHistory D s g q x) id
    (measurable_anisotropicFiniteRestartEnergyHistory D s g q x) measurable_id]
  · rw [anisotropicFiniteRestartEnergyHistory_law]
    rfl
  · intro sample
    rw [Measure.map_id]
    rfl

end QuantitativeFollowup
