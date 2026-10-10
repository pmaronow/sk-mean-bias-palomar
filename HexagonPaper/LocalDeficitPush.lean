module
public import QuantitativeFollowup.ConcentratingPushedDirection
public import QuantitativeFollowup.ConcentratingPushedContact

@[expose] public section

/-! Contact and sign on the actual concentrating segment for two
near-minimizers with the same budget, on any interior interval. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem local_deficit_pushed_delta_lower (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho a ell k tau theta eta : ℝ) (hbeta : 0 < beta)
    (hlam : lam ∈ Icc (0 : ℝ) beta) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hk : 0 ≤ k)
    (htau : tau ∈ Icc (0 : ℝ) (k*ell^2/64)) (htaupos : 0 < tau)
    (htheta : theta ∈ Icc (1/4 : ℝ) (3/4)) (heta : 0 ≤ eta)
    (hdensity : ENNReal.ofReal k • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell)))
    (hμ : μ ∈ scalarFloor (lam/beta)) (hν : ν ∈ scalarFloor (lam/beta))
    (hnearμ : followupEnergyFunctional n beta lam rho μ ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta)
    (hnearν : followupEnergyFunctional n beta lam rho ν ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta)
    (hbalance : rho*tau*(8*ell/15)=16*eta) :
    4*ell/15 ≤ vectorConcentratingDelta (n:=n)
      (concentratingPushedMix μ ν beta a ell k tau theta hbeta ha he hell hk htau hdensity)
        beta (1-rho) (lam/beta) (by linarith) a ell := by
  have hθ : theta ∈ Icc (0 : ℝ) 1 := ⟨by linarith [htheta.1],by linarith [htheta.2]⟩
  have hθpos : 0 < theta := by linarith [htheta.1]
  let P := concentratingPushedMix μ ν beta a ell k tau theta hbeta ha he hell hk htau hdensity
  have hnear : followupEnergyFunctional n beta lam rho (parisiMix μ ν theta) ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta := by
    have hm := followupEnergyFunctional_mix_le (n:=n) μ ν beta lam rho theta hbeta hlam.1 hrho.le hθ
    have h1 := mul_le_mul_of_nonneg_left hnearμ (sub_nonneg.mpr hθ.2)
    have h2 := mul_le_mul_of_nonneg_left hnearν hθ.1
    nlinarith
  have hf : P ∈ scalarFloor (lam/beta) :=
    concentratingPushedMix_mem_floor μ ν beta a ell k tau theta (lam/beta)
      hbeta ha he hell hk htau hθ hdensity hμ hν
  have hd := concentrating_admissible_nearmin_delta_lower hn (parisiMix μ ν theta) P
    beta lam rho a ell (theta*tau) eta hbeta hlam hrho ha he hell
    (mul_pos hθpos htaupos)
    (concentratingPushedMix_profile μ ν beta a ell k tau theta hbeta ha he hell hk htau hθ hdensity) hf hnear
  have hbal := congrArg (fun z : ℝ => theta*z) hbalance
  have hnum : 2*eta ≤ (8*ell/15/2)*(rho*(theta*tau)) := by
    nlinarith [mul_nonneg heta (show 0 ≤ 4*theta-1 by linarith [htheta.1])]
  have hsmall : 2*eta/(rho*(theta*tau)) ≤ 8*ell/15/2 :=
    (div_le_iff₀ (mul_pos hrho (mul_pos hθpos htaupos))).mpr hnum
  change 4*ell/15 ≤ vectorConcentratingDelta (n:=n) P beta (1-rho) (lam/beta) (by linarith) a ell
  linarith

theorem local_deficit_pushed_direction_sign (μ ν : Paper.ParisiMeasure)
    (beta a ell tau A : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau)
    (htausign : tau ≤ A*ell/8)
    (hgap : ∀x∈Ioo a (a+ell), A ≤ beta*parisiCDF ν x-beta*parisiCDF μ x) :
    ∀x∈Ioo a (a+ell), A/2 ≤ concentratingPushedDirection μ ν beta a ell tau x := by
  have hτ : tau*(4/ell) ≤ A/2 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hell).mpr
    nlinarith
  intro x hx
  have hchi := concentratingIntervalIncrement_bound a ell x hell
  have hh : tau*concentratingIntervalIncrement a ell x ≤ tau*(4/ell) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hchi) htau
  unfold concentratingPushedDirection
  linarith [hgap x hx]

end HexagonPaper
