module
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Fubini adapters retain the original history and original selected
payload. A second independent draw is represented by its actual constant
kernel. Integrability is transferred through the genuine associative
law, rather than assumed on every section. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedStreaming_integrable_compProd_fiber
    {H A : Type*} [MeasurableSpace H] [MeasurableSpace A]
    (M : Measure H) [SFinite M] (K : Kernel H A) [IsSFiniteKernel K]
    (F : H × A → ℝ) (hF : Integrable F (M ⊗ₘ K)) :
    Integrable (fun h => ∫ g, F (h, g) ∂K h) M := by
  change Integrable F ((Kernel.const Unit M ⊗ₖ Kernel.prodMkLeft Unit K) ()) at hF
  simpa only [Kernel.const_apply,Kernel.prodMkLeft_apply] using hF.integral_compProd

theorem cavityGeneratedStreaming_const_pair_kernel
    {H A B : Type*} [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace B]
    (K : Kernel H A) [IsSFiniteKernel K] (N : Measure B) [SFinite N] (h : H) :
    (K ⊗ₖ Kernel.const (H × A) N) h = (K h).prod N := by
  ext E hE
  rw [Kernel.compProd_apply hE,Measure.prod_apply hE]
  simp only [Kernel.const_apply]

theorem cavityGeneratedStreaming_integral_compProd_const_pair
    {H A B : Type*} [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace B]
    (M : Measure H) [SFinite M] (K : Kernel H A) [IsSFiniteKernel K]
    (N : Measure B) [SFinite N] (F : (H × A) × B → ℝ)
    (hF : Integrable F ((M ⊗ₘ K) ⊗ₘ Kernel.const (H × A) N)) :
    Integrable (fun h => ∫ z : A × B, F ((h, z.1), z.2) ∂(K h).prod N) M ∧
    (∫ z, F z ∂((M ⊗ₘ K) ⊗ₘ Kernel.const (H × A) N)) =
      ∫ h, ∫ z : A × B, F ((h, z.1), z.2) ∂(K h).prod N ∂M := by
  let L := M ⊗ₘ (K ⊗ₖ Kernel.const (H × A) N)
  let e : H × (A × B) ≃ᵐ (H × A) × B := MeasurableEquiv.prodAssoc.symm
  have he_apply (h : H) (z : A × B) : e (h, z) = ((h, z.1), z.2) := rfl
  have he : L.map e = (M ⊗ₘ K) ⊗ₘ Kernel.const (H × A) N := Measure.compProd_assoc
  have hL : Integrable (fun z => F (e z)) L :=
    e.measurableEmbedding.integrable_map_iff.mp (he.symm ▸ hF)
  have hi := cavityGeneratedStreaming_integrable_compProd_fiber M
    (K ⊗ₖ Kernel.const (H × A) N) (fun z => F (e z)) hL
  refine ⟨?_,?_⟩
  · simpa only [he_apply,cavityGeneratedStreaming_const_pair_kernel] using hi
  calc
    _ = ∫ z, F (e z) ∂L := by rw [←he,e.measurableEmbedding.integral_map]
    _ = ∫ h, ∫ z : A × B, F (e (h, z)) ∂(K ⊗ₖ Kernel.const (H × A) N) h ∂M :=
      Measure.integral_compProd hL
    _ = _ := by
      simp only [he_apply,cavityGeneratedStreaming_const_pair_kernel]

end QuantitativeFollowup
