module
public import FourPapersCommon.CompProdComapMap
public import Mathlib.Probability.Kernel.Composition.ParallelComp

@[expose] public section

/-! Product structure of two independent normalized conditional mark laws,
with their conditioning records retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 300000

theorem cavityIndependentMarkedProduct {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure A) (Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel A C) (η : Kernel B D) [IsMarkovKernel κ] [IsMarkovKernel η] :
    ((P.prod Q) ⊗ₘ (κ ∥ₖ η)).map
      (fun z : (A×B)×(C×D) => ((z.1.1,z.2.1),(z.1.2,z.2.2))) =
      (P ⊗ₘ κ).prod (Q ⊗ₘ η) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (by fun_prop) (hs.prod ht),
    Measure.compProd_apply ((by fun_prop : Measurable
      (fun z : (A×B)×(C×D) => ((z.1.1,z.2.1),(z.1.2,z.2.2)))) (hs.prod ht)),
    Measure.prod_prod, Measure.compProd_apply hs, Measure.compProd_apply ht]
  have he (x : A×B) :
      Prod.mk x ⁻¹' ((fun z : (A×B)×(C×D) => ((z.1.1,z.2.1),(z.1.2,z.2.2))) ⁻¹'
        (s ×ˢ t)) = (Prod.mk x.1 ⁻¹' s) ×ˢ (Prod.mk x.2 ⁻¹' t) := by
    ext y
    rfl
  simp_rw [he, Kernel.parallelComp_apply, Measure.prod_prod]
  exact lintegral_prod_mul (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
    (Kernel.measurable_kernel_prodMk_left ht).aemeasurable

end QuantitativeFollowup
