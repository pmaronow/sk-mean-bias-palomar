module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Measurability of actual variances from jointly measurable L² observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem measurable_parameter_variance (f : A×Ω→ℝ) (hf : Measurable f)
    (hL : ∀a,MemLp (fun ω=>f (a,ω)) 2 P) :
    Measurable (fun a=>variance (fun ω=>f (a,ω)) P) := by
  have hfirst:=(hf.stronglyMeasurable.integral_prod_right' (ν:=P)).measurable
  have hsecond:=((hf.pow_const 2).stronglyMeasurable.integral_prod_right' (ν:=P)).measurable
  have he : (fun a=>variance (fun ω=>f (a,ω)) P)=
      fun a=>(∫ω,f (a,ω)^2∂P)-(∫ω,f (a,ω)∂P)^2 := by
    funext a
    simpa only [Pi.pow_apply] using variance_eq_sub (hL a)
  rw [he]
  exact hsecond.sub (hfirst.pow_const 2)

end FourPapersCommon
