module
public import FourPapersCommon.ResponseCoercivity

@[expose] public section

/-! Literal coercivity from the genuine squared signal/energy estimate.
The analytic estimate is explicit at this generic arithmetic layer. -/
noncomputable section
namespace FourPapersCommon

theorem squared_response_coercivity (F rho A delta signal denom B d : ℝ)
    (hF : 0 ≤ F) (hrho : 0 < rho) (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (hB : 0 < B) (hd : 0 < d)
    (hsignal : A*delta/2 ≤ signal)
    (hresponse : rho*signal^2 ≤ F*denom)
    (hdenom : denom ≤ B+2*d*delta) :
    rho*A^2/72*min (delta^2/B) (delta/d) ≤ F := by
  have hsignal0 : 0 ≤ signal := (by positivity : 0 ≤ A*delta/2).trans hsignal
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ A*delta/2) hsignal 2
  have hc : rho*A^2*delta^2/4 ≤ F*(B+2*d*delta) := by
    have hh := (mul_le_mul_of_nonneg_left hs hrho.le).trans hresponse
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hdenom hF)
    nlinarith only [hh']
  have hfactor : 0 ≤ rho*A^2/72 := by positivity
  by_cases hcase : d*delta ≤ B
  · have hm : F*(B+2*d*delta) ≤ 3*F*B := by nlinarith
    have hh : rho*A^2/72*(delta^2/B) ≤ F := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ hB).mpr
      nlinarith [mul_nonneg hrho.le (mul_nonneg (sq_nonneg A) (sq_nonneg delta))]
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hfactor).trans hh
  · have hp : 0 < delta := pos_of_mul_pos_right (hB.trans (lt_of_not_ge hcase)) hd.le
    have hm : F*(B+2*d*delta) ≤ 3*F*d*delta := by nlinarith
    have hh : rho*A^2/72*(delta/d) ≤ F := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ hd).mpr
      apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith [mul_nonneg hrho.le (mul_nonneg (sq_nonneg A) (sq_nonneg delta))]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hfactor).trans hh

end FourPapersCommon
