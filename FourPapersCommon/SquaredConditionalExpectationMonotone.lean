module
public import Mathlib.Probability.CondVar
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

@[expose] public section

/-! The squared L² norm of conditional expectation increases with the
conditioning sigma-field. This supplies measurable scalar curves without
choosing jointly measurable pointwise conditional-expectation versions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω}

theorem integral_sq_condExp_mono [IsFiniteMeasure P]
    (m₁ m₂ : MeasurableSpace Ω) (h₁₂ : m₁≤m₂) (h₂ : m₂≤m₀)
    (F : Ω→ℝ) (hF : MemLp F 2 P) :
    (∫x,(P[F|m₁] x)^2∂P)≤∫x,(P[F|m₂] x)^2∂P := by
  letI : MeasurableSpace Ω:=m₀
  have hi : Integrable (fun x=>‖P[F|m₂] x‖^(2:ℝ)) P := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using
      (hF.condExp one_le_two (m:=m₂)).integrable_sq
  have h:=(integral_norm_condExp_rpow_le (m:=m₁) (by norm_num : (1:ℝ)≤2) hi)
  have he:=condExp_condExp_of_le (μ:=P) (f:=F) h₁₂ h₂
  have heq : (∫x,‖P[P[F|m₂]|m₁] x‖^(2:ℝ)∂P)=
      ∫x,(P[F|m₁] x)^2∂P := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    simp only [hx,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [heq] at h
  simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using h

theorem monotone_integral_sq_condExp {ι : Type*} [Preorder ι]
    [IsFiniteMeasure P] (m : ι→MeasurableSpace Ω)
    (hm : Monotone m) (hbound : ∀q,m q≤m₀) (F : Ω→ℝ) (hF : MemLp F 2 P) :
    Monotone (fun q=>∫x,(P[F|m q] x)^2∂P) := by
  intro r q hrq
  exact integral_sq_condExp_mono (m r) (m q) (hm hrq) (hbound q) F hF

end FourPapersCommon
