module
public import QuantitativeFollowup.RootRateArithmetic
public import QuantitativeFollowup.RootSmoothingWidth

@[expose] public section

/-! The literal inverse-width term in the root rate case analysis,
including zero mass. The curvature balance is an explicit arithmetic
input; it is not substituted for an actual response theorem. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

theorem root_mass_sqrt_scale (rho eta m : ℝ) (hrho : 0 < rho)
    (heta : 0 < eta) (hm : 0 ≤ m) :
    m*Real.sqrt (rho*m/eta)*(eta/rho)=(eta/rho)^((1 : ℝ)/2)*m^((3 : ℝ)/2) := by
  by_cases hm0 : m=0
  · simp [hm0]
  have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have hδ : 0 < eta/rho := div_pos heta hrho
  have hRatio : rho*m/eta=m/(eta/rho) := by field_simp
  have hSq := Real.sq_sqrt hδ.le
  have hS : Real.sqrt (eta/rho)≠0 := (Real.sqrt_pos.mpr hδ).ne'
  have hPower : m*Real.sqrt m=m^((3 : ℝ)/2) := by
    calc
      _ = m^(1 : ℝ)*m^((1 : ℝ)/2) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
      _ = m^((1 : ℝ)+1/2) := (Real.rpow_add hmp _ _).symm
      _ = _ := by norm_num
  calc
    _ = m*(Real.sqrt m/Real.sqrt (eta/rho))*(eta/rho) := by
      rw [hRatio,Real.sqrt_div hm]
    _ = Real.sqrt (eta/rho)*(m*Real.sqrt m) := by
      field_simp
      rw [hSq]
      field_simp
    _ = _ := by rw [hPower,Real.sqrt_eq_rpow]

theorem root_density_budget_bound (q eta rho m k C B : ℝ)
    (hq : 0 < q) (heta : 0 < eta) (hrho : 0 < rho) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hSmall : 8*m/q ≤ k)
    (hPower : q^4 ≤ B*(m/rootSmoothingWidth q eta rho m+C+k/4)*(eta/rho)) :
    q^4 ≤ B*(C+5*k/4)*(eta/rho)+B*(eta/rho)^((1 : ℝ)/2)*m^((3 : ℝ)/2) := by
  have hWidth := rootSmoothingWidth_inverse_bound q eta rho m hq heta hrho hm
  have hDensity : m/rootSmoothingWidth q eta rho m+C+k/4 ≤
      C+5*k/4+m*Real.sqrt (rho*m/eta) := by linarith
  have hScaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hDensity hB) (div_nonneg heta.le hrho.le)
  have hTerm := root_mass_sqrt_scale rho eta m hrho heta hm
  nlinarith

theorem root_density_case_rate (q eta rho m k C B : ℝ)
    (hq : 0 ≤ q) (heta : 0 < eta) (hrho : 0 < rho) (hetrho : eta ≤ rho)
    (hm : 0 ≤ m) (hk : 0 ≤ k) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hSmall : 8*m/q ≤ k)
    (hPower : q^4 ≤ B*(m/rootSmoothingWidth q eta rho m+C+k/4)*(eta/rho)) :
    q ≤ max ((2*B*(C+5*k/4))^((1 : ℝ)/4)) ((2*B)^((1 : ℝ)/4))*
      ((eta/rho)^((1 : ℝ)/6)+m) := by
  by_cases hq0 : q=0
  · subst q
    positivity
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  apply root_fourth_mixed_rate q B (C+5*k/4) (eta/rho) m hq hB (by positivity)
    ⟨div_nonneg heta.le hrho.le,(div_le_one hrho).mpr hetrho⟩ hm
  exact root_density_budget_bound q eta rho m k C B hqp heta hrho hm hB hSmall hPower

end QuantitativeFollowup
