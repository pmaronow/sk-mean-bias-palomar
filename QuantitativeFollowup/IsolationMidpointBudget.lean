module
public import QuantitativeFollowup.IsolationEndpoint

@[expose] public section

/-! Isolation endpoint arithmetic for a genuine midpoint gap. This
allows a weak-limit response proof to be consumed without postulating
second derivatives of the limiting functional. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000

theorem isolation_budget_of_midpoint (beta L c rho D eta m f₀ f₁ fHalf : ℝ)
    (hbeta : 1 ≤ beta) (hL : 1 ≤ L) (hc : 0 < c)
    (hrho : rho∈Ioc (0 : ℝ) 1) (hD : 0 ≤ D)
    (hMin : m ≤ fHalf)
    (hGap : c*isolationScale beta L c/4*rho^3*D^4 ≤ f₀+f₁-2*fHalf)
    (hBudget : f₀+f₁-2*m ≤
      rho*beta*(isolationScale beta L c*rho*D^2)^2/12+eta) :
    c*isolationScale beta L c/8*rho^3*D^4 ≤ eta := by
  have hb := (isolationScale_bounds beta L c hbeta hL hc).2.2.2
  have hm := mul_le_mul_of_nonneg_right hb
    (mul_nonneg (pow_nonneg hrho.1.le 3) (pow_nonneg hD 4))
  have he : rho*beta*(isolationScale beta L c*rho*D^2)^2/12 =
      (beta*(isolationScale beta L c)^2/12)*(rho^3*D^4) := by ring
  rw [he] at hBudget
  nlinarith only [hMin,hGap,hBudget,hm]

theorem isolation_rate_of_midpoint (beta L c rho D eta m f₀ f₁ fHalf : ℝ)
    (hbeta : 1 ≤ beta) (hL : 1 ≤ L) (hc : 0 < c)
    (hrho : rho∈Ioc (0 : ℝ) 1) (hD : D∈Icc (0 : ℝ) beta)
    (hMin : m ≤ fHalf)
    (hGap : c*isolationScale beta L c/4*rho^3*D^4 ≤ f₀+f₁-2*fHalf)
    (hBudget : f₀+f₁-2*m ≤
      rho*beta*(isolationScale beta L c*rho*D^2)^2/12+eta) :
    D ≤ isolationEndpointConstant beta (c*isolationScale beta L c/8)*
      min 1 (rho^((-3/4 : ℝ))*eta^((1/4 : ℝ))) := by
  have ha : 0 < c*isolationScale beta L c/8 := by
    have hs := isolationScale_pos beta L c (zero_lt_one.trans_le hbeta)
      (zero_lt_one.trans_le hL) hc
    positivity
  have hh := isolation_budget_of_midpoint beta L c rho D eta m f₀ f₁ fHalf
    hbeta hL hc hrho hD.1 hMin hGap hBudget
  have heta : 0 ≤ eta := (mul_nonneg
    (mul_nonneg ha.le (pow_nonneg hrho.1.le 3)) (pow_nonneg hD.1 4)).trans hh
  exact isolation_min_one_rate beta (c*isolationScale beta L c/8) rho D eta ha hrho.1
    hD.1 hD.2 heta hh

end QuantitativeFollowup
