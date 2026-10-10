module
public import QuantitativePaper.ResponseIntegralCauchySchwarz

@[expose] public section

/-! A scalar integral Cauchy–Schwarz consequence of an actual pointwise
quadratic bound, without square-root integrability assumptions. -/
noncomputable section
open MeasureTheory
namespace QuantitativePaper
variable {Ω : Type*} [MeasurableSpace Ω]

theorem response_nonnegative_quadratic {e p x : ℝ} (he : 0≤e) (hx : 0≤x)
    (hp : p^2≤e*x) (v : ℝ) : 0≤e*v^2+2*p*v+x := by
  by_cases he0 : e=0
  · have hp0 : p=0:=by nlinarith [sq_nonneg p]
    simp only [he0,hp0,zero_mul,mul_zero,zero_add]
    exact hx
  · have hepos : 0<e:=lt_of_le_of_ne he (Ne.symm he0)
    have hh : 0≤e*(e*v^2+2*p*v+x):=by nlinarith only [sq_nonneg (e*v+p),hp]
    exact (mul_nonneg_iff_of_pos_left hepos).mp hh

theorem response_integral_scalar_cauchy_schwarz
    (P : Measure Ω) (e p x : Ω→ℝ) (he : Integrable e P)
    (hp : Integrable p P) (hx : Integrable x P)
    (hn : ∀ᵐω∂P,0≤e ω ∧ 0≤x ω ∧ (p ω)^2≤e ω*x ω) :
    (∫ω,p ω∂P)^2≤(∫ω,e ω∂P)*(∫ω,x ω∂P) := by
  have hquad (v : ℝ) : 0≤(∫ω,e ω∂P)*(v*v)+(2*(∫ω,p ω∂P))*v+(∫ω,x ω∂P):=by
    have hh : 0≤∫ω,e ω*v^2+2*p ω*v+x ω∂P:=integral_nonneg_of_ae
      (hn.mono fun ω h=>response_nonnegative_quadratic h.1 h.2.1 h.2.2 v)
    have e₁:=integral_add ((he.mul_const (v^2)).add ((hp.const_mul 2).mul_const v)) hx
    have e₂:=integral_add (he.mul_const (v^2)) ((hp.const_mul 2).mul_const v)
    simp only [Pi.add_apply] at e₁ e₂
    rw [e₁,e₂,integral_mul_const,integral_mul_const,integral_const_mul] at hh
    nlinarith only [hh]
  have hd:=discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

end QuantitativePaper
