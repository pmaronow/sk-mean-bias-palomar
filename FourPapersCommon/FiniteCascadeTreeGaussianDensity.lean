module
public import FourPapersCommon.FiniteCascadeTreeCharges

@[expose] public section

/-! The actual initial Gaussian disorder tilt and its normalized joint law
with all fields and terminal spins of a finite genealogy. The same genuine
one-leaf normalizer is used for every tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

def finiteCascadeTreeGaussianNormalizer (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) (j : ℕ) (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  ∫ Q, Real.exp (s * finiteStateGaussianTerminalCascade V a L j Q)
    ∂finiteStateGaussianRawKernel R H

def finiteCascadeTreeGaussianJointLaw (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    Measure (FiniteStateField S × Records (FiniteStateField S) S T) :=
  ((finiteStateGaussianRawKernel R H).tilted
    (fun Q => s * finiteStateGaussianTerminalCascade V a L j Q)) ⊗ₘ
      finiteCascadeTreeRecordKernel V a L T

def finiteCascadeTreeGaussianReferenceLaw
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    Measure (FiniteStateField S × Records (FiniteStateField S) S T) :=
  (finiteStateGaussianRawKernel R H) ⊗ₘ finiteCascadeTreeReferenceKernel L T

theorem integrable_exp_finiteCascadeTreeGaussianInitial (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) (j : ℕ) (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) :
    Integrable (fun Q => Real.exp (s * finiteStateGaussianTerminalCascade V a L j Q))
      (finiteStateGaussianRawKernel R H) := by
  rw [finiteStateGaussianRawKernel_apply]
  apply (integrable_map_measure
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul s).exp.aestronglyMeasurable)
    (show Measurable (fun z => H + R z) from by fun_prop).aemeasurable).mpr
  exact integrable_exp_finiteStateGaussian_lipschitz _
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) R H s

theorem finiteCascadeTreeGaussianNormalizer_pos (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) (j : ℕ) (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) :
    0 < finiteCascadeTreeGaussianNormalizer V a L s j R H := by
  unfold finiteCascadeTreeGaussianNormalizer
  rw [finiteStateGaussianRawKernel_apply, integral_map (by fun_prop)
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul s).exp.aestronglyMeasurable)]
  exact integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz _
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) R H s)

theorem finiteCascadeTreeGaussianJointLaw_probability (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    IsProbabilityMeasure (finiteCascadeTreeGaussianJointLaw V a L s T R H) := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isProbabilityMeasure_tilted (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j R H)
  unfold finiteCascadeTreeGaussianJointLaw
  infer_instance

theorem finiteCascadeTreeGaussianJointLaw_density (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    finiteCascadeTreeGaussianJointLaw V a L s T R H =
      (finiteCascadeTreeGaussianReferenceLaw L T R H).withDensity (fun z => ENNReal.ofReal
        (Real.exp (finiteCascadeTreeTerminalEnergy V T z.1 z.2 -
          ((finiteCascadeTreeCharges V a L s T z.1 z.2).map (fun c => c.1 * c.2)).sum) /
            finiteCascadeTreeGaussianNormalizer V a L s j R H)) := by
  haveI := isFiniteKernel_finiteCascadeTreeReferenceKernel L T
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI : IsSFiniteKernel ((finiteCascadeTreeReferenceKernel L T).withDensity
      (fun Q z => ENNReal.ofReal (Real.exp (finiteCascadeTreeLogDensity V a L T Q z)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun Q z => ENNReal.ofReal_ne_top)
  have hm : Measurable (fun Q => ENNReal.ofReal (Real.exp
      (s * finiteStateGaussianTerminalCascade V a L j Q) /
        finiteCascadeTreeGaussianNormalizer V a L s j R H)) :=
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul s).exp.div_const _).ennreal_ofReal
  dsimp only [finiteCascadeTreeGaussianNormalizer] at hm
  unfold finiteCascadeTreeGaussianJointLaw finiteCascadeTreeGaussianReferenceLaw
  simp only [Measure.tilted]
  rw [finiteCascadeTreeRecordKernel_exp_density V a ha L T,
    Measure.withDensity_compProd_withDensity hm
      (measurable_finiteCascadeTreeLogDensity V a ha L T).exp.ennreal_ofReal]
  congr 1
  funext z
  change ENNReal.ofReal (Real.exp (s * finiteStateGaussianTerminalCascade V a L j z.1) /
      finiteCascadeTreeGaussianNormalizer V a L s j R H) *
    ENNReal.ofReal (Real.exp (finiteCascadeTreeLogDensity V a L T z.1 z.2)) = _
  rw [←ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le
    (finiteCascadeTreeGaussianNormalizer_pos V a ha L s j R H).le)]
  congr 1
  rw [div_mul_eq_mul_div, ←Real.exp_add, finiteCascadeTreeLogDensity_add_root_eq]

end FourPapersCommon
