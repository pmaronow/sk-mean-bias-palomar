module
public import QuantitativeFollowup.ConcentratingPushedMix

@[expose] public section

/-! Contact-size curvature mass along the genuine pushed mixing segment.
The budgets compare the actual functional to its actual compact minimum. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem followupEnergyFunctional_mix_le (μ ν : Paper.ParisiMeasure)
    (beta lam rho theta : ℝ) (hbeta : 0 < beta) (hlam : 0 ≤ lam) (hrho : 0 ≤ rho)
    (htheta : theta ∈ Icc (0 : ℝ) 1) :
    followupEnergyFunctional n beta lam rho (parisiMix μ ν theta) ≤
      (1-theta)*followupEnergyFunctional n beta lam rho μ+theta*followupEnergyFunctional n beta lam rho ν := by
  have hm := vectorMeasureFunctional_mix_le n μ ν beta (1-rho) (by linarith) (lam/beta)
    (div_nonneg hlam hbeta.le) theta htheta
  have hd := div_le_div_of_nonneg_right hm hbeta.le
  unfold followupEnergyFunctional
  convert hd using 1
  ring

theorem concentratingPushedMix_delta_lower (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho a ell kappa tau theta eta : ℝ) (hbeta : 0 < beta)
    (hlam : lam ∈ Icc (0 : ℝ) beta) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64)) (htaupos : 0 < tau)
    (htheta : theta ∈ Icc (1/4 : ℝ) (3/4)) (heta : 0 ≤ eta)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell)))
    (hμ : μ ∈ scalarFloor (lam/beta)) (hν : ν ∈ scalarFloor (lam/beta))
    (hnearμ : followupEnergyFunctional n beta lam rho μ ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta/12)
    (hnearν : followupEnergyFunctional n beta lam rho ν ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta)
    (hbalance : rho*tau*(8*ell/15)=6*eta) :
    4*ell/15 ≤ vectorConcentratingDelta (n:=n)
      (concentratingPushedMix μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau hdensity)
        beta (1-rho) (lam/beta) (by linarith) a ell := by
  have hθ : theta ∈ Icc (0 : ℝ) 1 := ⟨by linarith [htheta.1],by linarith [htheta.2]⟩
  have hθpos : 0 < theta := by linarith [htheta.1]
  let η' := (1-theta)*eta/12+theta*eta
  let P := concentratingPushedMix μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau hdensity
  have hnear : followupEnergyFunctional n beta lam rho (parisiMix μ ν theta) ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+η' := by
    have hm := followupEnergyFunctional_mix_le (n:=n) μ ν beta lam rho theta hbeta hlam.1 hrho.le hθ
    have h1 := mul_le_mul_of_nonneg_left hnearμ (sub_nonneg.mpr hθ.2)
    have h2 := mul_le_mul_of_nonneg_left hnearν hθ.1
    dsimp only [η']
    nlinarith
  have hf : P ∈ scalarFloor (lam/beta) :=
    concentratingPushedMix_mem_floor μ ν beta a ell kappa tau theta (lam/beta)
      hbeta ha he hell hkappa htau hθ hdensity hμ hν
  have hd := concentrating_admissible_nearmin_delta_lower hn (parisiMix μ ν theta) P
    beta lam rho a ell (theta*tau) η' hbeta hlam hrho ha he hell (mul_pos hθpos htaupos)
    (concentratingPushedMix_profile μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau hθ hdensity) hf hnear
  have hbal := congrArg (fun z : ℝ => theta*z) hbalance
  have hnum : 2*η' ≤ (8*ell/15/2)*(rho*(theta*tau)) := by
    dsimp only [η']
    nlinarith [mul_nonneg heta (show 0 ≤ 7*theta-1 by linarith [htheta.1])]
  have hsmall : 2*η'/(rho*(theta*tau)) ≤ 8*ell/15/2 :=
    (div_le_iff₀ (mul_pos hrho (mul_pos hθpos htaupos))).mpr hnum
  change 4*ell/15 ≤ vectorConcentratingDelta (n:=n) P beta (1-rho) (lam/beta) (by linarith) a ell
  linarith

end QuantitativeFollowup
