module
public import QuantitativeFollowup.ConcentratingEnergySegment
public import QuantitativeFollowup.VectorConcentratingDelta
public import QuantitativeFollowup.ReflectedFunctionalRegularization
public import QuantitativePaper.VectorMeasureMinimizer

@[expose] public section

/-! Actual concentrating cost and near-minimizer estimates. The proof uses
the closed first variation and convexity of the constructed vector functional,
with the true Hessian-energy response along the newly constructed profile. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem concentrating_energy_cost_le_response (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (beta lam rho a ell kappa tau : ℝ) (hbeta : 0 < beta) (hlam : 0 ≤ lam) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) :
    followupEnergyFunctional n beta lam rho
      (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity)-
        followupEnergyFunctional n beta lam rho μ ≤
      rho*tau/2 * (vectorConcentratingDelta (n:=n)
        (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity)
          beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15) := by
  let ν := concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity
  have ht : 1-rho < 1 := by linarith
  have hCDF (x : ℝ) : parisiCDF μ x-parisiCDF ν x = (tau/beta)*concentratingIntervalIncrement a ell x := by
    dsimp only [ν]
    rw [concentratingEnergyMeasure, concentratingParisiMeasure_cdf_all]
    ring
  have hp : (∫x in (0 : ℝ)..1, (parisiCDF μ x-parisiCDF ν x)*
      (vectorMeanOverlapReal (n:=n) ν beta (1-rho) (lam/beta) ht.le x-x)) =
      (tau/beta)*(8*ell/15-vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) ht.le a ell) := by
    calc
      _ = (tau/beta)*(∫x in (0 : ℝ)..1, concentratingIntervalIncrement a ell x *
        (vectorMeanOverlapReal (n:=n) ν beta (1-rho) (lam/beta) ht.le x-x)) := by
        rw [←intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        rw [hCDF]
        ring
      _ = _ := by rw [vector_concentrating_pairing ν beta (1-rho) (lam/beta) hbeta.ne' ht a ell ha he hell]
  have hv := vectorMeasureFunctional_convex_deficit_bound hn ν μ beta (1-rho) (lam/beta) hbeta.ne' ht
    (div_nonneg hlam hbeta.le)
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

theorem concentrating_energy_cost_le (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (beta lam rho a ell kappa tau : ℝ) (hbeta : 0 < beta) (hlam : 0 ≤ lam) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) :
    followupEnergyFunctional n beta lam rho
      (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity)-
        followupEnergyFunctional n beta lam rho μ ≤ rho*tau/2 := by
  have hc := concentrating_energy_cost_le_response hn μ beta lam rho a ell kappa tau hbeta hlam hrho ha he hell hkappa htau hdensity
  have hD := (vectorConcentratingDelta_mem_unit (n:=n)
    (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity)
    beta (1-rho) (lam/beta) hbeta.ne' (by linarith) a ell ha he hell).2
  apply hc.trans
  apply (mul_le_mul_of_nonneg_left (show _ ≤ (1 : ℝ) by linarith)
    (show 0 ≤ rho*tau/2 from div_nonneg (mul_nonneg hrho.le htau.1) (by norm_num))).trans_eq
  ring

def followupEnergyMinimum (n : ℕ) (hn : 0 < n) (beta lam rho : ℝ)
    (hbeta : 0 < beta) (hlam : lam ≤ beta) (hrho : 0 ≤ rho) : ℝ :=
  followupEnergyFunctional n beta lam rho
    (vectorMeasureMinimizer n hn beta (1-rho) (lam/beta) (by linarith) ((div_le_one hbeta).mpr hlam))

theorem followupEnergyMinimum_le (hn : 0 < n) (beta lam rho : ℝ)
    (hbeta : 0 < beta) (hlam : lam ≤ beta) (hrho : 0 ≤ rho)
    (μ : Paper.ParisiMeasure) (hμ : μ ∈ scalarFloor (lam/beta)) :
    followupEnergyMinimum n hn beta lam rho hbeta hlam hrho ≤ followupEnergyFunctional n beta lam rho μ :=
  div_le_div_of_nonneg_right (vectorMeasureMinimizer_minimal n hn beta (1-rho) (lam/beta)
    (by linarith) ((div_le_one hbeta).mpr hlam) μ hμ) hbeta.le

theorem concentrating_nearmin_delta_lower (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (beta lam rho a ell kappa tau eta : ℝ) (hbeta : 0 < beta) (hlam : lam ∈ Icc (0 : ℝ) beta) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32)) (htaupos : 0 < tau)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hfloor : μ ∈ scalarFloor (lam/beta))
    (hnear : followupEnergyFunctional n beta lam rho μ ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta) :
    8*ell/15 - 2*eta/(rho*tau) ≤ vectorConcentratingDelta (n:=n)
      (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity)
        beta (1-rho) (lam/beta) (by linarith) a ell := by
  let ν := concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity
  have hfloor' := concentratingEnergyMeasure_preserves_floor μ beta a ell kappa tau (lam/beta) hbeta ha he hell hkappa htau hdensity hfloor
  have hmin := followupEnergyMinimum_le hn beta lam rho hbeta hlam.2 hrho.le ν hfloor'
  have hcost := concentrating_energy_cost_le_response hn μ beta lam rho a ell kappa tau hbeta hlam.1 hrho ha he hell hkappa htau hdensity
  have hp : 0 < rho*tau := mul_pos hrho htaupos
  have hbalance : (8*ell/15-vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) (by linarith) a ell)*(rho*tau) ≤ 2*eta := by
    change followupEnergyFunctional n beta lam rho ν-followupEnergyFunctional n beta lam rho μ ≤ _ at hcost
    nlinarith
  -- Rearrange the genuine positive-denominator inequality.
  have htarget : 8*ell/15-vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) (by linarith) a ell ≤ 2*eta/(rho*tau) :=
    (le_div_iff₀ hp).mpr hbalance
  linarith

end QuantitativeFollowup
