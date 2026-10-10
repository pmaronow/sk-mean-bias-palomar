module
public import QuantitativeFollowup.RootPushedResponseData
public import QuantitativeFollowup.RootPushedEndpointBudget
public import QuantitativeFollowup.RootCurvatureBudget
public import QuantitativePaper.ResponseC1Midpoint

@[expose] public section

/-! Genuine actual-model curvature balance for the pushed root segment.
Finite response, weak convergence and Fatou give the true midpoint gap;
all minimum and endpoint costs come from the actual functional. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FourPapersCommon
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 2600000
variable {n : ℕ}

theorem root_pushed_midpoint_balance (hn : 0 < n)
    (P : ℝ → Paper.ParisiMeasure) (bar ν : Paper.ParisiMeasure)
    (beta lam rho q eta k d : ℝ) (hbeta : 0 < beta)
    (hlam : lam∈Icc (0 : ℝ) beta) (hrho : 0 < rho)
    (hq : q∈Ioc (0 : ℝ) (1/4)) (heta : 0 ≤ eta) (hk : 0 < k) (hd : 0 < d)
    (hFloor : ∀theta∈Icc (0 : ℝ) 1,P theta∈scalarFloor (lam/beta))
    (hProfile : ∀theta∈Icc (0 : ℝ) 1,∀x,
      beta*parisiCDF (P theta) x=beta*parisiCDF bar x+
        theta*concentratingPushedDirection bar ν beta (q/4) (q/2)
          (rootConcentratingStep rho q eta) x)
    (hContact : ∀theta∈Icc (1/4 : ℝ) (3/4),
      2*q/15 ≤ vectorConcentratingDelta (n:=n) (P theta)
        beta (1-rho) (lam/beta) (by linarith) (q/4) (q/2) ∧
      ENNReal.ofReal beta • (parisiCDFPrimitive (P theta)).measure.restrict (Ioo (q/4) (3*q/4)) ≤
        ENNReal.ofReal d • volume.restrict (Ioo (q/4) (3*q/4)))
    (hSign : ∀x∈Ioo (q/4) (3*q/4),k*q/16 ≤
      concentratingPushedDirection bar ν beta (q/4) (q/2) (rootConcentratingStep rho q eta) x)
    (hNearbar : followupEnergyFunctional n beta lam rho bar ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta/12)
    (hNearν : followupEnergyFunctional n beta lam rho ν ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta) :
    min (7*q^3/(3840*beta)) (2*q/(15*d)) ≤ (294912/k^2)*eta/(rho*q^3) := by
  let w := concentratingResponseTest (q/4) (q/2) (half_pos hq.1)
    (by linarith [hq.1]) (by linarith [hq.2])
  let Y := fun theta=>beta*512/(105*(q/2))+2*d*vectorConcentratingDelta (n:=n)
    (P theta) beta (1-rho) (lam/beta) (by linarith) (q/4) (q/2)
  have hData := root_pushed_response_data hn P bar _ beta lam rho q k d
    hbeta hrho hq hk hd hProfile hContact hSign
  have hCoeff : 0 ≤ rootResponseCurvature beta rho k q d := by
    unfold rootResponseCurvature
    positivity [hq.1]
  have hMid := response_C1_middle_midpoint_lower hn (P 0) (P 1) beta (1-rho) lam
    hbeta (by linarith) hlam.1 w Y (rootResponseCurvature beta rho k q d) hCoeff
    (fun theta ht=>(hData theta ht).1) (fun theta ht=>(hData theta ht).2.1) (by
      intro theta ht
      have hh := (hData theta ht).2.2
      simpa only [show 1-(1-rho)=rho by ring] using hh)
  have hMixHalf : P (1/2)=parisiMix (P 0) (P 1) (1/2) := by
    simpa only [mul_zero,zero_add,mul_one] using affine_profile_curve_mix P bar beta 0 1 _
      hbeta hProfile 0 1 (1/2) (by norm_num) (by norm_num) (by norm_num)
  have hMid' : 3*rootResponseCurvature beta rho k q d/16 ≤
      followupEnergyFunctional n beta lam rho (P 0)+followupEnergyFunctional n beta lam rho (P 1)-
        2*followupEnergyFunctional n beta lam rho (P (1/2)) := by
    simpa only [←hMixHalf,responseEnergyFunctional,followupEnergyFunctional] using hMid
  have hMin := followupEnergyMinimum_le hn beta lam rho hbeta hlam.2 hrho.le
    (P (1/2)) (hFloor (1/2) (by norm_num))
  have hBudgets := root_pushed_curve_endpoint_budget n hn P bar ν beta lam rho q eta
    hbeta hlam hrho hq heta hFloor hProfile hNearbar hNearν
  apply root_balance_of_midpoint_budget q eta rho k beta d _ _ _ hq heta hrho hk
    hBudgets.2.2.2.1 hBudgets.2.2.2.2
  have hh : 3*rootResponseCurvature beta rho k q d/16 ≤
      followupEnergyFunctional n beta lam rho (P 0)+followupEnergyFunctional n beta lam rho (P 1)-
        2*followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le := by
    linarith only [hMid',hMin]
  convert hh using 1
  unfold rootResponseCurvature
  ring

end QuantitativeFollowup
