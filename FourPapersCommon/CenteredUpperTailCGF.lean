module
public import FourPapersCommon.ExponentialQuadraticRemainder
public import FourPapersCommon.UpperTailExponentialMoment
public import Mathlib.Probability.Moments.Basic

@[expose] public section

/-! The actual centered logarithmic moment is controlled by a genuine upper
survival tail, including the contribution of its negative half. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace FourPapersCommon
set_option maxHeartbeats 1800000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem positive_part_weighted_square_bound (z a lam : ℝ) (ha : 0<a)
    (hlam : 0≤lam) (hla : lam≤a/2) :
    z^2*Real.exp (max (lam*z) 0) ≤ z^2+(8/a^2)*Real.exp (a*max z 0) := by
  by_cases hz : 0≤z
  · rw [max_eq_left hz,max_eq_left (mul_nonneg hlam hz)]
    have hq:=square_le_scaled_positive_exponential z a hz ha
    have he : Real.exp (lam*z)≤Real.exp (a*z/2):=by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hh:=(mul_le_mul hq he (Real.exp_pos _).le (by positivity)).trans_eq
      (show ((8/a^2)*Real.exp (a*z/2))*Real.exp (a*z/2)=
        (8/a^2)*Real.exp (a*z) by rw [mul_assoc,←Real.exp_add];congr 2 <;> ring)
    exact hh.trans (le_add_of_nonneg_left (sq_nonneg z))
  · have hz' : z≤0:=le_of_not_ge hz
    rw [max_eq_right hz',max_eq_right (mul_nonpos_of_nonneg_of_nonpos hlam hz')]
    simp only [Real.exp_zero,mul_one,mul_zero]
    exact le_add_of_nonneg_right (by positivity)

theorem centered_upper_tail_cgf_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZm : Measurable Z) (hZi : Integrable Z P)
    (hZsq : Integrable (fun w=>Z w^2) P) (hCenter : (∫w,Z w ∂P)=0)
    (a lam : ℝ) (ha : 0<a) (hlam : 0≤lam) (hla : lam≤a/2)
    (hExp : Integrable (fun w=>Real.exp (lam*Z w)) P)
    (hPosExp : Integrable (fun w=>Real.exp (a*max (Z w) 0)) P)
    (hTail : ∀u : ℝ,0<u → P.real {w | u≤Z w}≤3*Real.exp (-(2*a)*u)) :
    Real.log (∫w,Real.exp (lam*Z w) ∂P) ≤
      lam^2/2*((∫w,Z w^2 ∂P)+32/a^2) := by
  have hY : ∀w,0≤max (Z w) 0:=fun w=>le_max_right _ _
  have hYtail : ∀u : ℝ,0<u → P.real {w | u≤max (Z w) 0}≤
      3*Real.exp (-(2*a)*u):=by
    intro u hu
    have hs : {w | u≤max (Z w) 0}={w | u≤Z w}:=by
      ext w
      simp only [mem_setOf_eq,le_max_iff]
      constructor
      · rintro (h|h)
        · exact h
        · linarith
      · exact Or.inl
    rw [hs]
    exact hTail u hu
  have hMoment:=upper_tail_positive_exponential_integral P (fun w=>max (Z w) 0)
    (hZm.max measurable_const) hY (2*a) a ha (by linarith) hPosExp hYtail
  have hMoment4 : (∫w,Real.exp (a*max (Z w) 0) ∂P)≤4:=by
    have he : 1+3*a/(2*a-a)=4:=by field_simp [ha.ne'];ring
    rwa [he] at hMoment
  have hMajor : Integrable (fun w=>1+lam*Z w+
      (lam^2/2)*(Z w^2+(8/a^2)*Real.exp (a*max (Z w) 0))) P :=
    ((integrable_const 1).add (hZi.const_mul lam)).add
      ((hZsq.add (hPosExp.const_mul (8/a^2))).const_mul (lam^2/2))
  have hM:=integral_mono hExp hMajor (fun w=>by
    have ht:=exponential_quadratic_remainder_positive_part (lam*Z w)
    have hq:=positive_part_weighted_square_bound (Z w) a lam ha hlam hla
    have hmul:=mul_le_mul_of_nonneg_left hq (by positivity : 0≤lam^2/2)
    nlinarith)
  have hE : (∫w,1+lam*Z w+(lam^2/2)*(Z w^2+
      (8/a^2)*Real.exp (a*max (Z w) 0)) ∂P)=
      1+(lam^2/2)*((∫w,Z w^2 ∂P)+
        (8/a^2)*(∫w,Real.exp (a*max (Z w) 0) ∂P)) := by
    rw [integral_add (f:=fun w=>1+lam*Z w)
        (g:=fun w=>(lam^2/2)*(Z w^2+(8/a^2)*Real.exp (a*max (Z w) 0)))
        ((integrable_const 1).add (hZi.const_mul lam))
        ((hZsq.add (hPosExp.const_mul (8/a^2))).const_mul (lam^2/2)),
      integral_add (f:=fun _=>1) (g:=fun w=>lam*Z w)
        (integrable_const 1) (hZi.const_mul lam),
      integral_const,integral_const_mul,integral_const_mul,
      integral_add (f:=fun w=>Z w^2) (g:=fun w=>(8/a^2)*Real.exp (a*max (Z w) 0))
        hZsq (hPosExp.const_mul (8/a^2)),integral_const_mul,hCenter]
    simp only [probReal_univ,smul_eq_mul,one_mul,mul_zero,add_zero]
  rw [hE] at hM
  have hAux : (8/a^2)*(∫w,Real.exp (a*max (Z w) 0) ∂P)≤32/a^2 := by
    have hh:=mul_le_mul_of_nonneg_left hMoment4 (by positivity : 0≤8/a^2)
    convert hh using 1 <;> ring
  have hlog:=Real.log_le_sub_one_of_pos (integral_exp_pos hExp)
  have hh:=mul_le_mul_of_nonneg_left hAux (by positivity : 0≤lam^2/2)
  linarith

end FourPapersCommon
