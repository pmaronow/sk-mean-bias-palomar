module
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! A global scalar exponential Taylor bound using the positive part,
so one-sided exponential tail control suffices for centered cumulants. -/
noncomputable section
open Set
namespace FourPapersCommon
set_option maxHeartbeats 900000

theorem exponential_quadratic_remainder_positive_part (x : ℝ) :
    Real.exp x ≤ 1+x+x^2*Real.exp (max x 0)/2 := by
  by_cases hx0 : x=0
  · subst x
    norm_num
  have hx : (0:ℝ)≠x:=Ne.symm hx0
  obtain ⟨y,hy,he⟩:=taylor_mean_remainder_lagrange_iteratedDeriv
    (f:=Real.exp) (n:=1) hx (Real.contDiff_exp (n:=2)).contDiffOn
  have hderiv : derivWithin Real.exp (uIcc (0:ℝ) x) 0=1:=by
    simpa only [Real.exp_zero] using (Real.hasDerivAt_exp 0).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_uIcc hx 0 left_mem_uIcc)
  have hpoly : taylorWithinEval Real.exp 1 (uIcc (0:ℝ) x) 0 x=1+x:=by
    rw [show (1:ℕ)=0+1 by rfl,taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_one,hderiv]
    norm_num
  have hsecond : iteratedDeriv 2 Real.exp y=Real.exp y:=by
    have hh:=iteratedDeriv_exp_const_mul 2 (1:ℝ)
    simpa only [one_mul,one_pow] using congrFun hh y
  rw [hpoly,hsecond] at he
  norm_num only [sub_zero,Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat,Nat.cast_one] at he
  have hymax : y ≤ max x 0:=by
    have hh : y<max (0:ℝ) x:=hy.2
    simpa only [max_comm] using hh.le
  have hb:=mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hymax) (sq_nonneg x)
  nlinarith only [he,hb]

theorem square_le_scaled_positive_exponential (v a : ℝ) (hv : 0 ≤ v) (ha : 0<a) :
    v^2 ≤ 8/a^2*Real.exp (a*v/2) := by
  have hz : 0 ≤ a*v/2:=by positivity
  have hh:=Real.quadratic_le_exp_of_nonneg hz
  have he : (a*v/2)^2/2 ≤ Real.exp (a*v/2):=by nlinarith only [hh,hz]
  rw [show 8/a^2*Real.exp (a*v/2)=8*Real.exp (a*v/2)/a^2 by ring]
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith only [he]

end FourPapersCommon
