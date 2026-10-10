module
public import HexagonPaper.LocalDeficitResponse

@[expose] public section

/-! Four-way certificate arithmetic, including the failed room and
failed sign alternatives. The eventual constant depends only on beta. -/
noncomputable section
namespace HexagonPaper
open Set
set_option maxHeartbeats 2000000

def localDeficitMinimum (k ell A d0 d1 : ℝ) : ℝ :=
  min (k*ell^3) (min (A*ell^2)
    (min (A^2*ell^4) (A^2*ell^2/(d0+d1+k))))

def localDeficitCertificateConstant (beta : ℝ) : ℝ :=
  min (1/1920) (min (1/240) (min (7/(3133440*beta)) (1/24480)))

theorem local_deficit_certificate_constant_pos (beta : ℝ) (hbeta : 0 < beta) :
    0 < localDeficitCertificateConstant beta := by
  unfold localDeficitCertificateConstant
  positivity

theorem local_deficit_minimum_bounds (k ell A d0 d1 : ℝ) :
    localDeficitMinimum k ell A d0 d1 ≤ k*ell^3 ∧
    localDeficitMinimum k ell A d0 d1 ≤ A*ell^2 ∧
    localDeficitMinimum k ell A d0 d1 ≤ A^2*ell^4 ∧
    localDeficitMinimum k ell A d0 d1 ≤ A^2*ell^2/(d0+d1+k) := by
  unfold localDeficitMinimum
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem local_deficit_failed_room_bound (beta k ell A d0 d1 delta tau : ℝ)
    (hbeta : 0 < beta) (hk : 0 < k) (hell : 0 < ell)
    (hbalance : tau*ell=30*delta) (hroom : k*ell^2/64 < tau) :
    localDeficitCertificateConstant beta*localDeficitMinimum k ell A d0 d1 ≤ delta := by
  have hc := (local_deficit_certificate_constant_pos beta hbeta).le
  have hc1 : localDeficitCertificateConstant beta ≤ 1/1920 := min_le_left _ _
  have hδ : (1/1920)*(k*ell^3) ≤ delta := by
    have hh := mul_lt_mul_of_pos_right hroom hell
    nlinarith only [hh,hbalance]
  exact ((mul_le_mul_of_nonneg_left (local_deficit_minimum_bounds k ell A d0 d1).1 hc).trans
    (mul_le_mul_of_nonneg_right hc1 (by positivity))).trans hδ

theorem local_deficit_failed_sign_bound (beta k ell A d0 d1 delta tau : ℝ)
    (hbeta : 0 < beta) (hA : 0 < A) (hell : 0 < ell)
    (hbalance : tau*ell=30*delta) (hsign : A*ell/8 < tau) :
    localDeficitCertificateConstant beta*localDeficitMinimum k ell A d0 d1 ≤ delta := by
  have hc := (local_deficit_certificate_constant_pos beta hbeta).le
  have hc2 : localDeficitCertificateConstant beta ≤ 1/240 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδ : (1/240)*(A*ell^2) ≤ delta := by
    have hh := mul_lt_mul_of_pos_right hsign hell
    nlinarith only [hh,hbalance]
  exact ((mul_le_mul_of_nonneg_left (local_deficit_minimum_bounds k ell A d0 d1).2.1 hc).trans
    (mul_le_mul_of_nonneg_right hc2 (by positivity))).trans hδ

theorem local_deficit_curvature_budget_bound (beta rho k ell A d0 d1 eta tau : ℝ)
    (hbeta : 0 < beta) (hrho : 0 < rho) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hA : 0 < A) (hk : 0 < k) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (heta : 0 ≤ eta)
    (hbalance : rho*tau*ell=30*eta)
    (hbudget : 3*localDeficitResponseCurvature beta rho A ell (d0+d1+k)/16 ≤
      2*eta+rho*tau/2) :
    localDeficitCertificateConstant beta*localDeficitMinimum k ell A d0 d1 ≤ eta/rho := by
  let d := d0+d1+k
  have hd : 0 < d := by dsimp only [d]; positivity
  have hc := (local_deficit_certificate_constant_pos beta hbeta).le
  have hc3 : localDeficitCertificateConstant beta ≤ 7/(3133440*beta) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc4 : localDeficitCertificateConstant beta ≤ 1/24480 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [local_deficit_response_curvature_eq beta rho A ell _ hbeta hell] at hbudget
  have hpre : rho*A^2/384*min (7*ell^3/(480*beta)) (4*ell/(15*d)) ≤
      2*eta+rho*tau/2 := by
    convert hbudget using 1 <;> ring
  have hmult := mul_le_mul_of_nonneg_right hpre hell.le
  have hsmall : 2*eta*ell ≤ 2*eta := by nlinarith
  have hscaled : (rho*A^2/384*min (7*ell^3/(480*beta)) (4*ell/(15*d)))*ell ≤
      17*eta := by nlinarith only [hmult,hbalance,hsmall]
  by_cases hm : 7*ell^3/(480*beta) ≤ 4*ell/(15*d)
  · rw [min_eq_left hm] at hscaled
    have hδ : (7/(3133440*beta))*(A^2*ell^4) ≤ eta/rho := by
      apply (le_div_iff₀ hrho).mpr
      have hh : 17*(((7/(3133440*beta))*(A^2*ell^4))*rho) ≤ 17*eta := by
        convert hscaled using 1 <;> ring
      nlinarith only [hh]
    exact ((mul_le_mul_of_nonneg_left (local_deficit_minimum_bounds k ell A d0 d1).2.2.1 hc).trans
      (mul_le_mul_of_nonneg_right hc3 (by positivity))).trans hδ
  · rw [min_eq_right (le_of_not_ge hm)] at hscaled
    have hδ : (1/24480)*(A^2*ell^2/d) ≤ eta/rho := by
      apply (le_div_iff₀ hrho).mpr
      have hh : 17*(((1/24480)*(A^2*ell^2/d))*rho) ≤ 17*eta := by
        convert hscaled using 1 <;> ring
      nlinarith only [hh]
    exact ((mul_le_mul_of_nonneg_left (local_deficit_minimum_bounds k ell A d0 d1).2.2.2 hc).trans
      (mul_le_mul_of_nonneg_right hc4 (by positivity))).trans hδ

end HexagonPaper
