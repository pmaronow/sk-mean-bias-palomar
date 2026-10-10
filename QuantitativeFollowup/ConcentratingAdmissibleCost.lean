module
public import QuantitativeFollowup.ConcentratingDirectionConvexity

@[expose] public section

/-! Cost and near-minimizer bounds for arbitrary actual admissible
concentrating profiles, without a sufficient density-room restriction. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem concentrating_admissible_cost_response (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho a ell tau : ℝ) (hbeta : 0 < beta) (hlam : 0 ≤ lam) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell)
    (hprofile : ∀x, beta*parisiCDF ν x=beta*parisiCDF μ x-tau*concentratingIntervalIncrement a ell x) :
    followupEnergyFunctional n beta lam rho ν-followupEnergyFunctional n beta lam rho μ ≤
      rho*tau/2*(vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15) := by
  have ht : 1-rho < 1 := by linarith
  have hCDF (x : ℝ) : parisiCDF μ x-parisiCDF ν x=(tau/beta)*concentratingIntervalIncrement a ell x := by
    have hp := hprofile x
    field_simp
    nlinarith
  have hp : (∫x in (0 : ℝ)..1, (parisiCDF μ x-parisiCDF ν x)*
      (vectorMeanOverlapReal (n:=n) ν beta (1-rho) (lam/beta) ht.le x-x)) =
      (tau/beta)*(8*ell/15-vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) ht.le a ell) := by
    calc
      _ = (tau/beta)*(∫x in (0 : ℝ)..1, concentratingIntervalIncrement a ell x*
          (vectorMeanOverlapReal (n:=n) ν beta (1-rho) (lam/beta) ht.le x-x)) := by
        rw [←intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        rw [hCDF]
        ring
      _ = _ := by rw [vector_concentrating_pairing ν beta (1-rho) (lam/beta) hbeta.ne' ht a ell ha he hell]
  have hv := vectorMeasureFunctional_convex_deficit_bound hn ν μ beta (1-rho) (lam/beta)
    hbeta.ne' ht (div_nonneg hlam hbeta.le)
  rw [vectorOverlapDeficit_cdf_pairing, hp] at hv
  have hd := div_le_div_of_nonneg_right hv hbeta.le
  have halg : (((1-(1-rho))*beta^2)/2*((tau/beta)*(8*ell/15-
      vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) ht.le a ell)))/beta =
      rho*tau/2*(8*ell/15-vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) ht.le a ell) := by
    field_simp
    ring
  rw [halg, sub_div] at hd
  change vectorMeasureFunctional n ν beta (1-rho) (lam/beta)/beta-
    vectorMeasureFunctional n μ beta (1-rho) (lam/beta)/beta ≤ _
  linarith

theorem concentrating_admissible_cost_le (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho a ell tau : ℝ) (hbeta : 0 < beta) (hlam : 0 ≤ lam) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (htau : 0 ≤ tau)
    (hprofile : ∀x, beta*parisiCDF ν x=beta*parisiCDF μ x-tau*concentratingIntervalIncrement a ell x) :
    followupEnergyFunctional n beta lam rho ν-followupEnergyFunctional n beta lam rho μ ≤ rho*tau/2 := by
  apply (concentrating_admissible_cost_response hn μ ν beta lam rho a ell tau hbeta hlam hrho ha he hell hprofile).trans
  have hD := (vectorConcentratingDelta_mem_unit (n:=n) ν beta (1-rho) (lam/beta)
    hbeta.ne' (by linarith) a ell ha he hell).2
  have hm := mul_le_mul_of_nonneg_left (show
    vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15 ≤ 1 by linarith)
    (show 0 ≤ rho*tau/2 from div_nonneg (mul_nonneg hrho.le htau) (by norm_num))
  simpa only [mul_one] using hm

theorem concentrating_admissible_nearmin_delta_lower (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho a ell tau eta : ℝ) (hbeta : 0 < beta) (hlam : lam ∈ Icc (0 : ℝ) beta) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (htau : 0 < tau)
    (hprofile : ∀x, beta*parisiCDF ν x=beta*parisiCDF μ x-tau*concentratingIntervalIncrement a ell x)
    (hfloor : ν ∈ scalarFloor (lam/beta))
    (hnear : followupEnergyFunctional n beta lam rho μ ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta) :
    8*ell/15-2*eta/(rho*tau) ≤ vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) (by linarith) a ell := by
  have hmin := followupEnergyMinimum_le hn beta lam rho hbeta hlam.2 hrho.le ν hfloor
  have hcost := concentrating_admissible_cost_response hn μ ν beta lam rho a ell tau hbeta hlam.1 hrho ha he hell hprofile
  have hp : 0 < rho*tau := mul_pos hrho htau
  have hbalance : (8*ell/15-vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) (by linarith) a ell)*(rho*tau) ≤ 2*eta := by
    nlinarith
  have htarget : 8*ell/15-vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) (by linarith) a ell ≤ 2*eta/(rho*tau) :=
    (le_div_iff₀ hp).mpr hbalance
  linarith

end QuantitativeFollowup
