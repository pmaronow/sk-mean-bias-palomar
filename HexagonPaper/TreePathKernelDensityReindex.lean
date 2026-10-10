module
public import HexagonPaper.TreePathKernelDensity

@[expose] public section

/-! Starting a descendant path law at the genuine endpoint of its parent
edge is input reindexing of a kernel. Its density is reindexed by the
same measurable endpoint map. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

 theorem treePath_comap_withDensity {X Y Z : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] (e : X → Y) (he : Measurable e)
    (w : Y → Z → ℝ≥0∞) (hw : Measurable (Function.uncurry w)) :
    (κ.withDensity w).comap e he =
      (κ.comap e he).withDensity (fun x z => w (e x) z) := by
  have hw' : Measurable (Function.uncurry (fun x : X => fun z => w (e x) z)) :=
    hw.comp ((he.comp measurable_fst).prodMk measurable_snd)
  ext x : 1
  rw [Kernel.comap_apply, Kernel.withDensity_apply _ hw,
    Kernel.withDensity_apply _ hw', Kernel.comap_apply]

 theorem treePath_kernel_exp_density_endpoint_compProd {X Y Z W : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
    (κ : Kernel X Y) (η : Kernel Z W) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (e : X × Y → Z) (he : Measurable e) (f : X → Y → ℝ) (g : Z → W → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) ⊗ₖ
      ((η.withDensity (fun z w => ENNReal.ofReal (Real.exp (g z w)))).comap e he) =
      (κ ⊗ₖ η.comap e he).withDensity (fun x yw =>
        ENNReal.ofReal (Real.exp (f x yw.1 + g (e (x,yw.1)) yw.2))) := by
  rw [treePath_comap_withDensity η e he (fun z w => ENNReal.ofReal (Real.exp (g z w))) hg.exp.ennreal_ofReal]
  exact treePath_kernel_exp_density_compProd κ (η.comap e he) f
    (fun xy w => g (e xy) w) hf
    (hg.comp ((he.comp measurable_fst).prodMk measurable_snd))

end HexagonPaper
