module
public import QuantitativeFollowup.LocalizationLevelBounds

@[expose] public section

/-! The exact four-case arithmetic in localization, including zero
curvature and fractional powers. The four level-set estimates remain
explicit inputs; this module does not assume or assert a model response
inequality. -/
noncomputable section
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000

theorem fourth_power_fourth_root (x : ℝ) (hx : 0≤x) : (x^((1 : ℝ)/4))^4=x := by
  convert Real.rpow_inv_natCast_pow hx (by norm_num : (4 : ℕ)≠0) using 1
  norm_num

theorem cube_third_root (x : ℝ) (hx : 0≤x) : (x^((1 : ℝ)/3))^3=x := by
  convert Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ)≠0) using 1
  norm_num

theorem cube_two_thirds (x : ℝ) (hx : 0≤x) : (x^((2/3 : ℝ)))^3=x^2 := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx]
  norm_num

 theorem quartic_term_coercivity (D K rho : ℝ) (hD : 0≤D) (hK : 0≤K) (hrho : 0<rho)
    (hlarge : D≤(8/3 : ℝ)*(K/rho)^((1 : ℝ)/4)) :
    (3/8 : ℝ)^4*rho*D^4≤K := by
  have hp := pow_le_pow_left₀ hD hlarge 4
  rw [mul_pow,fourth_power_fourth_root _ (div_nonneg hK hrho.le)] at hp
  have hh : (3/8 : ℝ)^4*D^4≤K/rho := by nlinarith
  convert (le_div_iff₀ hrho).mp hh using 1
  ring

 theorem sqrt_term_coercivity (D K h : ℝ) (hD : 0≤D) (hK : 0≤K) (hh : 0<h)
    (hlarge : D≤4*Real.sqrt (K/h)) : h*D^2/16≤K := by
  have hp := pow_le_pow_left₀ hD hlarge 2
  rw [mul_pow,Real.sq_sqrt (div_nonneg hK hh.le)] at hp
  have hs : D^2/16≤K/h := by nlinarith
  convert (le_div_iff₀ hh).mp hs using 1
  ring

 theorem cubic_term_coercivity (D K rho beta : ℝ) (hD : 0≤D) (hDb : D≤beta)
    (hK : 0≤K) (hrho : 0<rho) (hbeta : 0<beta)
    (hlarge : D≤6*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3)) :
    rho*D^4/(216*beta^2)≤K := by
  have hp := pow_le_pow_left₀ hD hlarge 3
  rw [mul_pow,mul_pow,cube_third_root _ hbeta.le,cube_third_root _ (div_nonneg hK hrho.le)] at hp
  have hfirst : rho*D^3/(216*beta)≤K := by
    have hh : D^3/(216*beta)≤K/rho :=
      (div_le_iff₀ (by positivity : 0<216*beta)).mpr (by nlinarith)
    convert (le_div_iff₀ hrho).mp hh using 1
    ring
  have hD43 : D^4≤beta*D^3 := by
    have hh := mul_le_mul_of_nonneg_right hDb (pow_nonneg hD 3)
    nlinarith
  calc
    _ ≤ rho*(beta*D^3)/(216*beta^2) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr (mul_le_mul_of_nonneg_left hD43 hrho.le)
    _ = rho*D^3/(216*beta) := by field_simp
    _ ≤ K := hfirst

 theorem two_thirds_term_coercivity (D K h beta L : ℝ) (hD : 0≤D) (hDb : D≤beta)
    (hK : 0≤K) (hh : 0<h) (hbeta : 0<beta) (hL : 0<L)
    (hlarge : D≤3*(K/h)^((2/3 : ℝ))/(2*L)^((1 : ℝ)/3)) :
    (Real.sqrt (2*L)/(3*Real.sqrt 3*Real.sqrt beta))*h*D^2≤K := by
  have hp := pow_le_pow_left₀ hD hlarge 3
  rw [div_pow,mul_pow,cube_two_thirds _ (div_nonneg hK hh.le),cube_third_root _ (by positivity)] at hp
  have hs : (2*L)*D^3≤27*(K/h)^2 := by
    have hx := (le_div_iff₀ (by positivity : 0<2*L)).mp hp
    norm_num at hx
    nlinarith
  have hD43 : D^4≤beta*D^3 := by
    have hx := mul_le_mul_of_nonneg_right hDb (pow_nonneg hD 3)
    nlinarith
  have hs4 : (2*L)*D^4≤27*beta*(K/h)^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hD43 (by positivity : 0≤2*L)
    have h₂ := mul_le_mul_of_nonneg_left hs hbeta.le
    nlinarith
  have hscaled : (2*L)*h^2*D^4≤27*beta*K^2 := by
    have hm := mul_le_mul_of_nonneg_right hs4 (sq_nonneg h)
    have he : (K/h)^2*h^2=K^2 := by field_simp
    nlinarith
  let c := Real.sqrt (2*L)/(3*Real.sqrt 3*Real.sqrt beta)
  have hc : 0≤c := by dsimp only [c]; positivity
  have hcsq : c^2=(2*L)/(27*beta) := by
    dsimp only [c]
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤2*L),
      Real.sq_sqrt (by norm_num : (0 : ℝ)≤3),Real.sq_sqrt hbeta.le]
    norm_num
  have hsquare : (c*h*D^2)^2≤K^2 := by
    have he : (c*h*D^2)^2=((2*L)*h^2*D^4)/(27*beta) := by rw [mul_pow,mul_pow,hcsq]; ring
    rw [he]
    exact (div_le_iff₀ (by positivity : 0<27*beta)).mpr (by nlinarith)
  exact (pow_le_pow_iff_left₀ (by positivity : 0≤c*h*D^2) hK (by norm_num : (2 : ℕ)≠0)).mp hsquare

def localizationCaseConstant (beta L : ℝ) : ℝ :=
  min ((3/8 : ℝ)^4) (min (1/16) (min (1/(216*beta^2))
    (Real.sqrt (2*L)/(3*Real.sqrt 3*Real.sqrt beta))))

theorem localizationCaseConstant_pos (beta L : ℝ) (hbeta : 0<beta) (hL : 0<L) :
    0<localizationCaseConstant beta L := by
  unfold localizationCaseConstant
  positivity

theorem localization_case_combination (D K rho h beta L : ℝ)
    (hD : 0≤D) (hDb : D≤beta) (hK : 0≤K) (hrho : 0<rho)
    (hh : 0<h) (hbeta : 0<beta) (hL : 0<L)
    (hcases :
      D≤(4/3 : ℝ)*(K/rho)^((1 : ℝ)/4)+2*Real.sqrt (K/h) ∨
      D≤3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3)+3*(K/h)^((2/3 : ℝ))/(2*(2*L)^((1 : ℝ)/3)) ∨
      D≤3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3)+2*Real.sqrt (K/h)) :
    localizationCaseConstant beta L*min (rho*D^4) (h*D^2)≤K := by
  have hc := localizationCaseConstant_pos beta L hbeta hL
  have h₁ : localizationCaseConstant beta L≤(3/8 : ℝ)^4 := min_le_left _ _
  have h₂ : localizationCaseConstant beta L≤1/16 := (min_le_right _ _).trans (min_le_left _ _)
  have h₃ : localizationCaseConstant beta L≤1/(216*beta^2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₄ : localizationCaseConstant beta L≤Real.sqrt (2*L)/(3*Real.sqrt 3*Real.sqrt beta) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfirst (hx : (3/8 : ℝ)^4*rho*D^4≤K) :
      localizationCaseConstant beta L*min (rho*D^4) (h*D^2)≤K := by
    exact ((mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le).trans
      (by nlinarith [mul_le_mul_of_nonneg_right h₁ (by positivity : 0≤rho*D^4)])).trans hx
  have hsecond (hx : h*D^2/16≤K) :
      localizationCaseConstant beta L*min (rho*D^4) (h*D^2)≤K := by
    exact ((mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le).trans
      (by nlinarith [mul_le_mul_of_nonneg_right h₂ (by positivity : 0≤h*D^2)])).trans hx
  have hthird (hx : rho*D^4/(216*beta^2)≤K) :
      localizationCaseConstant beta L*min (rho*D^4) (h*D^2)≤K := by
    calc
      _ ≤ localizationCaseConstant beta L*(rho*D^4) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
      _ ≤ (1/(216*beta^2))*(rho*D^4) :=
        mul_le_mul_of_nonneg_right h₃ (by positivity)
      _ = rho*D^4/(216*beta^2) := by ring
      _ ≤ K := hx
  have hfourth (hx : (Real.sqrt (2*L)/(3*Real.sqrt 3*Real.sqrt beta))*h*D^2≤K) :
      localizationCaseConstant beta L*min (rho*D^4) (h*D^2)≤K := by
    exact ((mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le).trans
      (by nlinarith [mul_le_mul_of_nonneg_right h₄ (by positivity : 0≤h*D^2)])).trans hx
  rcases hcases with hcase | hcase | hcase
  · by_cases hlarge : D/2≤(4/3 : ℝ)*(K/rho)^((1 : ℝ)/4)
    · exact hfirst (quartic_term_coercivity D K rho hD hK hrho (by linarith))
    · exact hsecond (sqrt_term_coercivity D K h hD hK hh (by linarith))
  · by_cases hlarge : D/2≤3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3)
    · exact hthird (cubic_term_coercivity D K rho beta hD hDb hK hrho hbeta (by linarith))
    · have he : 2*(3*(K/h)^((2/3 : ℝ))/(2*(2*L)^((1 : ℝ)/3))) =
          3*(K/h)^((2/3 : ℝ))/(2*L)^((1 : ℝ)/3) := by ring
      exact hfourth (two_thirds_term_coercivity D K h beta L hD hDb hK hh hbeta hL
        (by rw [←he]; linarith))
  · by_cases hlarge : D/2≤3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3)
    · exact hthird (cubic_term_coercivity D K rho beta hD hDb hK hrho hbeta (by linarith))
    · exact hsecond (sqrt_term_coercivity D K h hD hK hh (by linarith))

end QuantitativeFollowup
