module
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Actual finite-measure identification from the real sine and cosine
Fourier test integrals. Integrability follows from their literal unit bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

theorem finiteMeasure_eq_of_cos_sin {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hc : ∀ L : E→L[ℝ] ℝ,(∫ x,Real.cos (L x) ∂μ)=∫ x,Real.cos (L x) ∂ν)
    (hs : ∀ L : E→L[ℝ] ℝ,(∫ x,Real.sin (L x) ∂μ)=∫ x,Real.sin (L x) ∂ν) : μ=ν := by
  apply Measure.ext_of_charFunDual
  funext L
  have hi (ρ : Measure E) [IsFiniteMeasure ρ] :
      Integrable (fun x=>Complex.exp ((L x : ℂ)*Complex.I)) ρ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun x=>by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFunDual_apply,charFunDual_apply,←integral_re_add_im (hi μ),←integral_re_add_im (hi ν)]
  simp only [RCLike.re_eq_complex_re,RCLike.im_eq_complex_im,
    Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
  rw [hc L,hs L]

end FourPapersCommon
