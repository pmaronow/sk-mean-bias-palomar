module
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-! Actual transport of both coordinates of a probability-kernel sampling
law from an exact sectional sampling law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

theorem map_compProd_map_pair (μ : Measure A) [SFinite μ]
    (κ : Kernel A B) [IsSFiniteKernel κ] (η : Kernel C D) [IsSFiniteKernel η]
    (f : A→C) (g : B→D) (hf : Measurable f) (hg : Measurable g)
    (hsection : ∀a,(κ a).map g=η (f a)) :
    (μ⊗ₘκ).map (Prod.map f g)=μ.map f⊗ₘη := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap hg) hs,Measure.compProd_apply ((hf.prodMap hg) hs),
    Measure.compProd_apply hs,lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr
  intro a
  rw [←hsection a,Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

end FourPapersCommon
