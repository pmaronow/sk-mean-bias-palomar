module
public import FourPapersCommon.ConditionalKernelFourier
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-! The actual conditional expectation under an arbitrary state-space
transition law, retaining every event in the complete chosen past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

theorem condExp_kernel_of_restricted_transitionLaw {Ω : Type*} (m₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm₀ : m₀ ≤ mΩ)
    (X Y : Ω → E) (hX : StronglyMeasurable[m₀] X) (hY : Measurable Y)
    (κ : Kernel E E) [IsMarkovKernel κ]
    (hlaw : ∀ A : Set Ω, MeasurableSet[m₀] A → (P.restrict A).map Y =
      κ ∘ₘ (P.restrict A).map X)
    (f : E → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    P[(fun sample => f (Y sample)) | m₀] =ᵐ[P]
      fun sample => ∫ y, f y ∂κ (X sample) := by
  have hkernel := stronglyMeasurable_kernelObservable κ f hf
  have hcand : StronglyMeasurable[m₀] (fun sample => ∫ y, f y ∂κ (X sample)) :=
    hkernel.comp_measurable hX.measurable
  have hi : Integrable (fun sample => f (Y sample)) P :=
    (integrable_const C).mono' (hf.comp hY).aestronglyMeasurable (.of_forall fun sample => hC _)
  have hci : Integrable (fun sample => ∫ y, f y ∂κ (X sample)) P :=
    (integrable_const C).mono' (hcand.mono hm₀).aestronglyMeasurable (.of_forall fun sample => by
      simpa using norm_integral_le_of_norm_le_const (μ := κ (X sample)) (.of_forall hC))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm₀ hi
  · intro A hA hfinite
    exact hci.integrableOn
  · intro A hA hfinite
    have he : (∫ y, f y ∂(P.restrict A).map Y) =
        ∫ y, f y ∂(κ ∘ₘ (P.restrict A).map X) := by rw [hlaw A hA]
    rw [integral_map hY.aemeasurable hf.aestronglyMeasurable,
      integral_kernel_comp_bounded _ κ f hf C hC,
      integral_map (hX.mono hm₀).measurable.aemeasurable hkernel.aestronglyMeasurable] at he
    exact he.symm
  · exact hcand.aestronglyMeasurable


end FourPapersCommon
