module
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-! Compositional path-kernel density algebra.
These identities hold on arbitrary measurable path/record spaces, with no
finite Gaussian or finite-profile restriction. They are the genuine
withDensity product and sequential product identities used when building
full path genealogies. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem treePath_prodMkLeft_withDensity {X Y Z : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] (w : Y → Z → ℝ≥0∞) (hw : Measurable (Function.uncurry w)) :
    Kernel.prodMkLeft X (κ.withDensity w) =
      (Kernel.prodMkLeft X κ).withDensity (fun p z => w p.2 z) := by
  have hw' : Measurable (Function.uncurry (fun p : X × Y => fun z => w p.2 z)) :=
    hw.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  ext p : 1
  rw [Kernel.prodMkLeft_apply, Kernel.withDensity_apply _ hw,
    Kernel.withDensity_apply _ hw', Kernel.prodMkLeft_apply]

theorem treePath_kernel_exp_density_prod {X Y Z : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (κ : Kernel X Y) (η : Kernel X Z)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (f : X → Y → ℝ) (g : X → Z → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) ×ₖ
      (η.withDensity (fun x z => ENNReal.ofReal (Real.exp (g x z)))) =
      (κ ×ₖ η).withDensity (fun x yz => ENNReal.ofReal (Real.exp (f x yz.1 + g x yz.2))) := by
  haveI : IsSFiniteKernel (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) :=
    Kernel.IsSFiniteKernel.withDensity κ (fun x y => ENNReal.ofReal_ne_top)
  haveI : IsSFiniteKernel (η.withDensity (fun x z => ENNReal.ofReal (Real.exp (g x z)))) :=
    Kernel.IsSFiniteKernel.withDensity η (fun x z => ENNReal.ofReal_ne_top)
  ext x : 1
  rw [Kernel.prod_apply, Kernel.withDensity_apply _ hf.exp.ennreal_ofReal,
    Kernel.withDensity_apply _ hg.exp.ennreal_ofReal,
    MeasureTheory.prod_withDensity (by fun_prop) (by fun_prop),
    Kernel.withDensity_apply _ (by fun_prop), Kernel.prod_apply]
  congr 1
  funext yz
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem treePath_kernel_exp_density_compProd {X Y Z : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (κ : Kernel X Y) (η : Kernel (X × Y) Z)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (f : X → Y → ℝ) (g : X × Y → Z → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) ⊗ₖ
      (η.withDensity (fun xy z => ENNReal.ofReal (Real.exp (g xy z)))) =
      (κ ⊗ₖ η).withDensity (fun x yz => ENNReal.ofReal (Real.exp (f x yz.1 + g (x,yz.1) yz.2))) := by
  haveI : IsSFiniteKernel (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) :=
    Kernel.IsSFiniteKernel.withDensity κ (fun x y => ENNReal.ofReal_ne_top)
  haveI : IsSFiniteKernel (η.withDensity (fun xy z => ENNReal.ofReal (Real.exp (g xy z)))) :=
    Kernel.IsSFiniteKernel.withDensity η (fun xy z => ENNReal.ofReal_ne_top)
  haveI : IsSFiniteKernel ((κ ⊗ₖ η).withDensity (fun x yz => ENNReal.ofReal (Real.exp (f x yz.1)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun x yz => ENNReal.ofReal_ne_top)
  simp only [Kernel.compProd_withDensity (κ:=κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y))))
      (η:=η) (g:=fun xy z => ENNReal.ofReal (Real.exp (g xy z))) hg.exp.ennreal_ofReal,
    Kernel.withDensity_compProd (κ:=κ) (η:=η)
      (g:=fun x y => ENNReal.ofReal (Real.exp (f x y))) hf.exp.ennreal_ofReal]
  ext x : 1
  rw [Kernel.withDensity_apply _ (by fun_prop), Kernel.withDensity_apply _ (by fun_prop),
    Kernel.withDensity_apply _ (by fun_prop), ←MeasureTheory.withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext yz
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl


end HexagonPaper
