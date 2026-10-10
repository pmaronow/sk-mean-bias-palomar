module
public import QuantitativeFollowup.RootRoomCase
public import QuantitativeFollowup.RootPowerCaseRate

@[expose] public section

/-! Exact coefficient and branch reduction for root localization. The
room-available curvature balance remains an explicit arithmetic input;
it must be discharged by the genuine actual functional response. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def rootQuantileCoefficient (beta k C T : ℝ) : ℝ :=
  T⁻¹*max (16/k) (max (2*(1440/k)^((1 : ℝ)/3)) (rootPowerCaseConstant beta k C))

theorem rootQuantileCoefficient_ge_eight (beta k C T : ℝ)
    (hk : 0 < k) (hT : 0 < T) (hkT : k*T ≤ 2) :
    8 ≤ rootQuantileCoefficient beta k C T := by
  have hFirst : 16/k/T ≤ rootQuantileCoefficient beta k C T := by
    unfold rootQuantileCoefficient
    have hh := mul_le_mul_of_nonneg_left (le_max_left (16/k)
      (max (2*(1440/k)^((1 : ℝ)/3)) (rootPowerCaseConstant beta k C))) (inv_nonneg.mpr hT.le)
    convert hh using 1
    ring
  have hEight : 8 ≤ 16/k/T := by
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hk hT)).mpr
    nlinarith
  exact hEight.trans hFirst

theorem root_quantile_arithmetic (Q beta k C T lam v eta rho m : ℝ)
    (hQ : Q ∈ Icc (0 : ℝ) 1) (hbeta : 0 < beta) (hk : 0 < k) (hC : 0 ≤ C)
    (hT : T ∈ Ioc (0 : ℝ) (1/4)) (hkT : k*T ≤ 2)
    (hlam : 0 ≤ lam) (hv : 0 ≤ v) (heta : 0 < eta) (hrho : 0 < rho)
    (hm : 0 ≤ m) (hmv : m ≤ v)
    (hBalance :
      16*(lam+v) < k*min Q T →
      rootConcentratingStep rho (min Q T) eta ≤ (k/2)*((min Q T)/2)^2/64 →
      min (7*(min Q T)^3/(3840*beta))
        (2*(min Q T)/(15*(m/rootSmoothingWidth (min Q T) eta rho m+C+k/4))) ≤
      rootBalanceConstant k*(eta/rho)/(min Q T)^3) :
    Q ≤ rootQuantileCoefficient beta k C T*
      (lam+v+min 1 ((eta/rho)^((1 : ℝ)/6))) := by
  have hCoefficient := rootQuantileCoefficient_ge_eight beta k C T hk hT.1 hkT
  have hCoefficient0 : 0 ≤ rootQuantileCoefficient beta k C T := by linarith
  by_cases hBig : rho ≤ eta
  · have hδ : 1 ≤ eta/rho := (one_le_div hrho).mpr hBig
    have hRoot : 1 ≤ (eta/rho)^((1 : ℝ)/6) := Real.one_le_rpow hδ (by norm_num)
    rw [min_eq_left hRoot]
    nlinarith [mul_nonneg hCoefficient0 (add_nonneg hlam hv),hQ.2]
  have hδ : eta/rho ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg heta.le hrho.le,(div_le_one hrho).mpr (le_of_not_ge hBig)⟩
  have hRoot : (eta/rho)^((1 : ℝ)/6) ≤ 1 := Real.rpow_le_one hδ.1 hδ.2 (by norm_num)
  rw [min_eq_right hRoot]
  let q := min Q T
  let S := lam+v+(eta/rho)^((1 : ℝ)/6)
  let K := max (16/k) (max (2*(1440/k)^((1 : ℝ)/3)) (rootPowerCaseConstant beta k C))
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hq0 : 0 ≤ q := le_min hQ.1 hT.1.le
  have hq : q ≤ T := min_le_right _ _
  have hBound : q ≤ K*S := by
    by_cases hSmall : k*q ≤ 16*(lam+v)
    · have hSmall' : q ≤ (16/k)*(lam+v) := by
        rw [show (16/k)*(lam+v)=16*(lam+v)/k by ring]
        apply (le_div_iff₀ hk).mpr
        nlinarith
      calc
        q ≤ (16/k)*(lam+v) := hSmall'
        _ ≤ (16/k)*S := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_right (Real.rpow_nonneg hδ.1 _)
        _ ≤ K*S := mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    have hLarge : 16*(lam+v) < k*q := lt_of_not_ge hSmall
    have hqp : 0 < q := by nlinarith
    by_cases hRoom : rootConcentratingStep rho q eta ≤ (k/2)*(q/2)^2/64
    · have hb := root_power_case_rate q eta rho m v lam beta k C hqp heta hrho
        (le_of_not_ge hBig) hm hmv hlam hbeta hk hC hLarge.le (hBalance hLarge hRoom)
      calc
        q ≤ rootPowerCaseConstant beta k C*S := by
          convert hb using 1 <;> ring
        _ ≤ K*S := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_right _ _)) hS
    · have hb := root_room_failure_rate rho q eta k hrho hqp hk ⟨heta.le,le_of_not_ge hBig⟩ hRoom
      calc
        q ≤ 2*(1440/k)^((1 : ℝ)/3)*(eta/rho)^((1 : ℝ)/6) := hb
        _ ≤ 2*(1440/k)^((1 : ℝ)/3)*S := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          dsimp only [S]
          linarith
        _ ≤ K*S := mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_right _ _)) hS
  have hQT : Q ≤ q/T := root_quantile_reduction Q T hQ ⟨hT.1,by linarith [hT.2]⟩
  calc
    Q ≤ q/T := hQT
    _ ≤ K*S/T := div_le_div_of_nonneg_right hBound hT.1.le
    _ = rootQuantileCoefficient beta k C T*S := by
      dsimp only [rootQuantileCoefficient,K]
      ring

end QuantitativeFollowup
