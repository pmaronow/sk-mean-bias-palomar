module
public import QuantitativeFollowup.IsolationBudget
public import QuantitativeFollowup.LocalizationCaseCombination

@[expose] public section

/-! The exact fractional-power endpoint of isolation, including zero
error. The functional curvature and endpoint budget are explicit analytic
inputs; the resulting rate arithmetic does not assume the desired rate. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem quartic_rate_bound (a rho D eta : ℝ) (ha : 0<a) (hrho : 0<rho)
    (hD : 0≤D) (heta : 0≤eta) (hbudget : a*rho^3*D^4≤eta) :
    D ≤ a^((-1/4 : ℝ))*rho^((-3/4 : ℝ))*eta^((1/4 : ℝ)) := by
  have ha4 : (a^((-1/4 : ℝ)))^4=a⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ha.le]
    norm_num [Real.rpow_neg_one]
  have hr4 : (rho^((-3/4 : ℝ)))^4=(rho^3)⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hrho.le]
    norm_num [Real.rpow_neg hrho.le,Real.rpow_natCast]
  have hpow : (a^((-1/4 : ℝ))*rho^((-3/4 : ℝ))*eta^((1/4 : ℝ)))^4 =
      eta/(a*rho^3) := by
    rw [mul_pow,mul_pow,ha4,hr4,fourth_power_fourth_root eta heta]
    ring
  apply (pow_le_pow_iff_left₀ hD (by positivity) (by norm_num : (4 : ℕ)≠0)).mp
  rw [hpow]
  exact (le_div_iff₀ (by positivity : 0<a*rho^3)).mpr (by nlinarith [hbudget])

def isolationEndpointConstant (beta a : ℝ) : ℝ := max beta (a^((-1/4 : ℝ)))

theorem isolationEndpointConstant_pos (beta a : ℝ) (ha : 0<a) :
    0 < isolationEndpointConstant beta a :=
  (Real.rpow_pos_of_pos ha _).trans_le (le_max_right _ _)

theorem isolation_min_one_rate (beta a rho D eta : ℝ) (ha : 0<a) (hrho : 0<rho)
    (hD : 0≤D) (hDb : D≤beta) (heta : 0≤eta) (hbudget : a*rho^3*D^4≤eta) :
    D ≤ isolationEndpointConstant beta a *
      min 1 (rho^((-3/4 : ℝ))*eta^((1/4 : ℝ))) := by
  have hc := isolationEndpointConstant_pos beta a ha
  have hfirst : D ≤ isolationEndpointConstant beta a := hDb.trans (le_max_left _ _)
  have hsecond : D ≤ isolationEndpointConstant beta a*(rho^((-3/4 : ℝ))*eta^((1/4 : ℝ))) := by
    calc
      _ ≤ a^((-1/4 : ℝ))*rho^((-3/4 : ℝ))*eta^((1/4 : ℝ)) :=
        quartic_rate_bound a rho D eta ha hrho hD heta hbudget
      _ = a^((-1/4 : ℝ))*(rho^((-3/4 : ℝ))*eta^((1/4 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  rw [mul_min_of_nonneg _ _ hc.le,mul_one]
  exact le_min hfirst hsecond

theorem isolation_rate_of_second_derivative (beta L c rho D eta m : ℝ)
    (hbeta : 1≤beta) (hL : 1≤L) (hc : 0<c)
    (hrho : rho∈Ioc (0 : ℝ) 1) (hD : D∈Ioc (0 : ℝ) beta)
    (f f' f'' : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf' : ∀x∈Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'' : ∀x∈Ioo (0 : ℝ) 1, HasDerivAt f' (f'' x) x)
    (hcurv : ∀x∈Ioo (0 : ℝ) 1,
      c*rho^2*min (rho*D^4) ((isolationScale beta L c*rho*D^2)*D^2) ≤ f'' x)
    (hmin : m≤f (1/2))
    (hbudget : f 0+f 1-2*m≤rho*beta*(isolationScale beta L c*rho*D^2)^2/12+eta) :
    D ≤ isolationEndpointConstant beta (c*isolationScale beta L c/8) *
      min 1 (rho^((-3/4 : ℝ))*eta^((1/4 : ℝ))) := by
  have ha : 0<c*isolationScale beta L c/8 := by
    have hs := isolationScale_pos beta L c (zero_lt_one.trans_le hbeta)
      (zero_lt_one.trans_le hL) hc
    positivity
  have hg := isolation_budget_of_second_derivative beta L c rho D eta m hbeta hL hc
    hrho hD f f' f'' hf hf' hf'' hcurv hmin hbudget
  have heta : 0≤eta := (mul_nonneg (mul_nonneg ha.le (pow_nonneg hrho.1.le 3))
    (pow_nonneg hD.1.le 4)).trans hg
  exact isolation_min_one_rate beta (c*isolationScale beta L c/8) rho D eta ha hrho.1
    hD.1.le hD.2 heta hg

end QuantitativeFollowup
