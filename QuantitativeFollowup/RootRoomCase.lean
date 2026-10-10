module
public import QuantitativeFollowup.RootPushedSegment
public import QuantitativeFollowup.RootRateArithmetic

@[expose] public section

/-! Exact concentrating-room equivalence and the small-radius rate when
room fails. These are genuine algebraic supporting displays and do not
assume a model localization bound. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

theorem rootConcentratingStep_room_iff (rho q eta k : ℝ)
    (hrho : 0 < rho) (hq : 0 < q) (hk : 0 < k) :
    rootConcentratingStep rho q eta ≤ (k/2)*(q/2)^2/64 ↔
      1440*eta/k ≤ rho*(q/2)^3 := by
  unfold rootConcentratingStep
  rw [div_le_iff₀ (by positivity : 0 < 2*rho*q),div_le_iff₀ hk]
  constructor <;> intro h <;> nlinarith

theorem root_room_failure_rate (rho q eta k : ℝ)
    (hrho : 0 < rho) (hq : 0 < q) (hk : 0 < k)
    (heta : eta ∈ Icc (0 : ℝ) rho)
    (hFailure : ¬rootConcentratingStep rho q eta ≤ (k/2)*(q/2)^2/64) :
    q ≤ 2*(1440/k)^((1 : ℝ)/3)*(eta/rho)^((1 : ℝ)/6) := by
  have hδ : eta/rho ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg heta.1 hrho.le,(div_le_one hrho).mpr heta.2⟩
  have hδ0 : 0 ≤ eta/rho := hδ.1
  have hFail := not_le.mp ((rootConcentratingStep_room_iff rho q eta k hrho hq hk).not.mp hFailure)
  have hPower : q^3 ≤ (11520/k)*(eta/rho) := by
    rw [show (11520/k)*(eta/rho)=11520*eta/(rho*k) by field_simp]
    apply (le_div_iff₀ (mul_pos hrho hk)).mpr
    have hf := (lt_div_iff₀ hk).mp hFail
    nlinarith
  have hqRoot : q ≤ 2*(1440/k)^((1 : ℝ)/3)*(eta/rho)^((1 : ℝ)/3) := by
    apply (pow_le_pow_iff_left₀ hq.le (by positivity) (by norm_num : (3 : ℕ)≠0)).mp
    rw [mul_pow,mul_pow]
    have h₁ : ((1440/k)^((1 : ℝ)/3))^3=1440/k := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ 1440/k)]
      norm_num
    have h₂ : ((eta/rho)^((1 : ℝ)/3))^3=eta/rho := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hδ.1]
      norm_num
    rw [h₁,h₂]
    convert hPower using 1
    ring
  calc
    q ≤ 2*(1440/k)^((1 : ℝ)/3)*(eta/rho)^((1 : ℝ)/3) := hqRoot
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge' hδ.1 hδ.2 (by norm_num) (by norm_num)) (by positivity)

end QuantitativeFollowup
