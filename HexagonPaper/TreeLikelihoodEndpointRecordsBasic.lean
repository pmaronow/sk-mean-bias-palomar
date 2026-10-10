module
public import HexagonPaper.TreePathKernelDensityTree
public import Mathlib.Probability.Kernel.Composition.CompMap

@[expose] public section

/-! Mapping recorded full paths to their actual endpoints preserves the
conditional continuation kernel. This proof concerns finite Markov kernels,
so equality on measurable rectangles suffices. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HexagonPaper
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
variable {X Y Z W : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace W]

theorem endpointRecord_compProd_map (κ : Kernel X Y) (η : Kernel X Z)
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (f : Y → X) (g : Z → W) (hf : Measurable f) (hg : Measurable g) :
    (κ ⊗ₖ η.comap (fun p : X × Y => f p.2) (hf.comp measurable_snd)).map
      (Prod.map f g) = (Kernel.id ×ₖ η.map g) ∘ₖ κ.map f := by
  rw [← Kernel.compProd_prodMkLeft_eq_comp]
  ext x : 1
  apply Measure.ext_prod
  intro s t hs ht
  rw [Kernel.map_apply' _ (hf.prodMap hg) _ (hs.prod ht)]
  change (κ ⊗ₖ η.comap (fun p : X × Y => f p.2) (hf.comp measurable_snd)) x
    ((f ⁻¹' s) ×ˢ (g ⁻¹' t)) = _
  rw [Kernel.compProd_apply_prod (hf hs) (hg ht),
    Kernel.compProd_apply_prod hs ht]
  simp only [Kernel.comap_apply, Kernel.prodMkLeft_apply]
  rw [Kernel.map_apply _ hf,
    setLIntegral_map hs ((η.map g).measurable_coe ht) hf]
  congr 1
  funext y
  exact (Kernel.map_apply' η hg (f y) ht).symm

end HexagonPaper
