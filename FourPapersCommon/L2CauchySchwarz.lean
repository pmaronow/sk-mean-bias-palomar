module
public import FourPapersCommon.L2IntegralBounds

@[expose] public section

/-! Cauchy--Schwarz for actual Bochner expectations, including the
zero-second-moment case. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem integral_mul_square_le (f g : Ω→ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ω,f ω*g ω∂P)^2≤(∫ω,f ω^2∂P)*(∫ω,g ω^2∂P) := by
  have hi : ⟪hf.toLp f,hg.toLp g⟫=∫ω,f ω*g ω∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with ω hfw hgw
    simp [RCLike.inner_apply,hfw,hgw,mul_comm]
  have hh:=real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [hi,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,norm_sq_toLp,norm_sq_toLp] at hh
  simpa only [pow_two] using hh

theorem integral_mul_abs_le_sqrt_product (f g : Ω→ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |∫ω,f ω*g ω∂P|≤Real.sqrt ((∫ω,f ω^2∂P)*(∫ω,g ω^2∂P)) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs] using integral_mul_square_le f g hf hg

theorem integral_mul_abs_le_sqrt_moment_bounds (f g : Ω→ℝ)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) (A B : ℝ)
    (hfA : (∫ω,f ω^2∂P)≤A) (hgB : (∫ω,g ω^2∂P)≤B) :
    |∫ω,f ω*g ω∂P|≤Real.sqrt (A*B) := by
  apply (integral_mul_abs_le_sqrt_product f g hf hg).trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul hfA hgB (integral_nonneg (fun _=>sq_nonneg _))
    ((integral_nonneg (fun _=>sq_nonneg _)).trans hfA)

end FourPapersCommon
