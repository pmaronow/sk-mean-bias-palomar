module
public import QuantitativeFollowup.FollowupCavityFiniteTreeLaw
public import FourPapersCommon.FiniteCascadeTreeGaussianDensity

@[expose] public section

/-! Genuine initial-disorder normalization and full recorded density for the
anisotropic cavity genealogy. Its terminal-spin marginal is the actual
previously constructed cavity tree law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open FourPapersCommon FiniteTerminalGenealogy QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def anisotropicRootEnergyMap (D : AnisotropicSpinModel n) :
    AnisotropicDisorder n →L[ℝ] FiniteStateField (Configuration n) :=
  (anisotropicEnergyMap D).comp (anisotropicDisorderInjection n)

theorem anisotropicFiniteInitialLaw_energy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    (anisotropicFiniteInitialLaw D s a).map (anisotropicEnergyMap D) =
      (finiteStateGaussianRawKernel (anisotropicRootEnergyMap D) 0).tilted
        (fun H => a * finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
          (anisotropicSchemeMass s) (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j))
            (k+2) H) := by
  unfold anisotropicFiniteInitialLaw
  rw [Measure.map_map (anisotropicEnergyMap D).continuous.measurable
    (anisotropicDisorderInjection n).continuous.measurable,
    finiteStateGaussianRawKernel_apply]
  simp only [zero_add]
  rw [OverlapPaper.tilted_map_eq _ _ (anisotropicRootEnergyMap D).continuous.measurable _
    (((contDiff_one_finiteStateGaussianTerminalCascade _ _ (anisotropicSchemeMass_nonneg s) _ (k+2)).continuous.measurable.const_mul a))]
  rfl

def anisotropicFiniteRecordedTreeLaw (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) :=
  finiteCascadeTreeGaussianJointLaw (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a T
      (anisotropicRootEnergyMap D) 0

instance anisotropicFiniteRecordedTreeLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) :
    IsProbabilityMeasure (anisotropicFiniteRecordedTreeLaw D s a T) :=
  finiteCascadeTreeGaussianJointLaw_probability _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

private theorem kernel_comp_map_measure {X Y Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure X) (κ : Kernel Y Z)
    (f : X → Y) (hf : Measurable f) :
    κ ∘ₘ (μ.map f) = (κ.comap f hf) ∘ₘ μ := by
  ext B hB
  rw [Measure.bind_apply hB κ.aemeasurable,
    Measure.bind_apply hB (Kernel.aemeasurable _),
    lintegral_map (κ.measurable_coe hB) hf]
  rfl

theorem anisotropicFiniteRecordedTreeLaw_spin_marginal (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) :
    (anisotropicFiniteRecordedTreeLaw D s a T).map
      (fun z => spins T z.2) = anisotropicFiniteTreeLaw D s a (asGenealogy T) := by
  let V := fun _ : Configuration n => (0 : ℝ)
  let L := fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)
  let K := finiteCascadeTreeRecordKernel V (anisotropicSchemeMass s) L T
  haveI : IsMarkovKernel K := isMarkovKernel_finiteCascadeTreeRecordKernel V _ (anisotropicSchemeMass_nonneg s) L T
  haveI := isProbabilityMeasure_tilted (integrable_exp_finiteCascadeTreeGaussianInitial V _
    (anisotropicSchemeMass_nonneg s) L a (k+2) (anisotropicRootEnergyMap D) 0)
  change (_ ⊗ₘ K).map (spins T ∘ Prod.snd) = _
  dsimp only [K] at *
  rw [←Measure.map_map (measurable_spins T) measurable_snd,
    ←Measure.snd,Measure.snd_compProd,Measure.map_comp _ _ (measurable_spins T)]
  rw [show K.map (spins T) = finiteCascadeGenealogyKernel V (anisotropicSchemeMass s) L (asGenealogy T)
    from finiteCascadeTreeRecordKernel_spin_marginal V _ (anisotropicSchemeMass_nonneg s) L T,
    ←anisotropicFiniteInitialLaw_energy D s a,
    kernel_comp_map_measure _ _ _ (anisotropicEnergyMap D).continuous.measurable]
  rfl

theorem anisotropicFiniteRecordedTreeLaw_density (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) :
    anisotropicFiniteRecordedTreeLaw D s a T =
      (finiteCascadeTreeGaussianReferenceLaw
        (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) T
        (anisotropicRootEnergyMap D) 0).withDensity (fun z => ENNReal.ofReal
          (Real.exp (finiteCascadeTreeTerminalEnergy (fun _ : Configuration n => 0) T z.1 z.2 -
            ((finiteCascadeTreeCharges (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
              (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a T z.1 z.2).map
                (fun c => c.1*c.2)).sum) /
                  finiteCascadeTreeGaussianNormalizer (fun _ : Configuration n => 0)
                    (anisotropicSchemeMass s)
                    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j))
                    a (k+2) (anisotropicRootEnergyMap D) 0)) :=
  finiteCascadeTreeGaussianJointLaw_density _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

end QuantitativeFollowup
