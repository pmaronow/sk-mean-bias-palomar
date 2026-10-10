module
public import FourPapersCommon.ConditionalKernelExpectation

@[expose] public section

/-! Genuine weighted conditional-kernel identity for any integrable past
weight. This includes unbounded exponential initial-disorder densities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
variable {Ω : Type*}

theorem weighted_kernelObservable_of_condExp_integrable
    (m₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (hm₀ : m₀≤mΩ)
    (g k : Ω→ℝ) (hg : Integrable g P) (hcond : P[g | m₀]=ᵐ[P] k)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[m₀] Z) (hZg : Integrable (Z*g) P) :
    (∫sample,Z sample*g sample ∂P)=∫sample,Z sample*k sample ∂P := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hZ hZg hg
  have hprod : (Z*P[g | m₀])=ᵐ[P] (fun sample=>Z sample*k sample) := by
    filter_upwards [hcond] with sample hs
    simp only [Pi.mul_apply]
    rw [hs]
  have he := integral_congr_ae (hpull.trans hprod)
  have ht := MeasureTheory.integral_condExp (μ:=P) (f:=Z*g) hm₀
  simpa only [Pi.mul_apply] using ht.symm.trans he

end FourPapersCommon
