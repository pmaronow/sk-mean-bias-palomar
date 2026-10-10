module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! The literal square-root response follows from the stronger squared
energy inequality. No response estimate is hidden in the arithmetic. -/
noncomputable section
namespace FourPapersCommon

theorem squareRoot_response_of_squared {rho F Y Z S : ℝ}
    (hrho : 0<rho) (hF : 0≤F) (hY : 0≤Y) (hZ : 0≤Z)
    (h : rho^3*S^2≤F*(Y+2*Z)) :
    rho*|S|≤Real.sqrt (F/rho)*(Real.sqrt Y+2*Real.sqrt (Y+Z)) := by
  have ha := Real.sq_sqrt (div_nonneg hF hrho.le)
  have hb := Real.sq_sqrt (show 0≤Y+2*Z by positivity)
  have hs : (rho*|S|)^2≤(Real.sqrt (F/rho)*Real.sqrt (Y+2*Z))^2 := by
    rw [mul_pow,mul_pow,ha,hb,sq_abs]
    have hh : rho^2*S^2≤F*(Y+2*Z)/rho :=
      (le_div_iff₀ hrho).mpr (by nlinarith only [h])
    simpa only [div_mul_eq_mul_div] using hh
  have hsmall : rho*|S|≤Real.sqrt (F/rho)*Real.sqrt (Y+2*Z) :=
    (sq_le_sq₀ (mul_nonneg hrho.le (abs_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hs
  have hlarge : Real.sqrt (Y+2*Z)≤2*Real.sqrt (Y+Z) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0≤2*Real.sqrt (Y+Z))).mp
    rw [Real.sq_sqrt (by positivity),mul_pow,Real.sq_sqrt (by positivity)]
    nlinarith
  apply hsmall.trans
  exact mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg Y]) (Real.sqrt_nonneg _)

end FourPapersCommon
