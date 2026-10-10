module
public import FourPapersCommon.FourierMeasureEquality
public import FourPapersCommon.FiniteJointLaw

@[expose] public section

/-! Actual restricted transition laws from whole-past sine/cosine identities.
The restriction retains arbitrary events in the past sigma algebra. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

theorem stronglyMeasurable_kernelObservable (κ : Kernel E E) [IsMarkovKernel κ]
    (f : E → ℝ) (hf : Measurable f) :
    StronglyMeasurable (fun x => ∫ y, f y ∂κ x) :=
  ((hf.comp measurable_snd).stronglyMeasurable).integral_kernel_prod_right'

theorem integral_kernel_comp_bounded (P : Measure E) [IsFiniteMeasure P]
    (κ : Kernel E E) [IsMarkovKernel κ] (f : E → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ y, f y ∂(κ ∘ₘ P)) = ∫ x, (∫ y, f y ∂κ x) ∂P := by
  have hi : Integrable f (κ ∘ₘ P) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (.of_forall hC)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  rfl

theorem integral_indicator_one_mul_eq_setIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (f : Ω → ℝ) :
    (∫ sample, A.indicator (fun _ => (1 : ℝ)) sample * f sample ∂P) =
      ∫ sample in A, f sample ∂P := by
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact .of_forall fun sample => by
    by_cases hsample : sample ∈ A <;> simp [hsample]

theorem restricted_transitionLaw_of_weighted_fourier {Ω : Type*} (m₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm₀ : m₀ ≤ mΩ)
    (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (κ : Kernel E E) [IsMarkovKernel κ]
    (hcos : ∀ (L : E→L[ℝ] ℝ) (Z : Ω → ℝ), Measurable[m₀] Z →
      (∀ sample, ‖Z sample‖ ≤ (1 : ℝ)) →
      (∫ sample, Z sample * Real.cos (L (Y sample)) ∂P) =
        ∫ sample, Z sample * (∫ y, Real.cos (L y) ∂κ (X sample)) ∂P)
    (hsin : ∀ (L : E→L[ℝ] ℝ) (Z : Ω → ℝ), Measurable[m₀] Z →
      (∀ sample, ‖Z sample‖ ≤ (1 : ℝ)) →
      (∫ sample, Z sample * Real.sin (L (Y sample)) ∂P) =
        ∫ sample, Z sample * (∫ y, Real.sin (L y) ∂κ (X sample)) ∂P)
    (A : Set Ω) (hA : MeasurableSet[m₀] A) :
    (P.restrict A).map Y = κ ∘ₘ (P.restrict A).map X := by
  have hAg : MeasurableSet A := hm₀ A hA
  have hZ : Measurable[m₀] (A.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hA
  have hZb : ∀ sample, ‖A.indicator (fun _ => (1 : ℝ)) sample‖ ≤ (1 : ℝ) := by
    intro sample
    by_cases hsample : sample ∈ A <;> simp [hsample]
  apply finiteMeasure_eq_of_cos_sin
  · intro L
    have he := hcos L _ hZ hZb
    rw [integral_indicator_one_mul_eq_setIntegral P A hAg,
      integral_indicator_one_mul_eq_setIntegral P A hAg] at he
    rw [integral_map hY.aemeasurable (by fun_prop : AEStronglyMeasurable
      (fun y : E => Real.cos (L y)) ((P.restrict A).map Y)),
      integral_kernel_comp_bounded _ κ (fun y => Real.cos (L y)) (by fun_prop) 1
        (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (L y)),
      integral_map hX.aemeasurable
        (stronglyMeasurable_kernelObservable κ _ (by fun_prop)).aestronglyMeasurable]
    exact he
  · intro L
    have he := hsin L _ hZ hZb
    rw [integral_indicator_one_mul_eq_setIntegral P A hAg,
      integral_indicator_one_mul_eq_setIntegral P A hAg] at he
    rw [integral_map hY.aemeasurable (by fun_prop : AEStronglyMeasurable
      (fun y : E => Real.sin (L y)) ((P.restrict A).map Y)),
      integral_kernel_comp_bounded _ κ (fun y => Real.sin (L y)) (by fun_prop) 1
        (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (L y)),
      integral_map hX.aemeasurable
        (stronglyMeasurable_kernelObservable κ _ (by fun_prop)).aestronglyMeasurable]
    exact he


end FourPapersCommon
