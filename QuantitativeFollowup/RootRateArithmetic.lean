module
public import QuantitativeFollowup.Absorption
public import Mathlib.Tactic

@[expose] public section

/-! The sixth-power and mixed fourth-power case analysis in root
localization. These are unconditional real inequalities, with the
curvature balance kept explicitly separate from the actual model. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem root_sixth_power (x : ℝ) (hx : 0 ≤ x) : (x^((1 : ℝ)/6))^6=x := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx]
  norm_num

theorem root_fourth_power (x : ℝ) (hx : 0 ≤ x) : (x^((1 : ℝ)/4))^4=x := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx]
  norm_num

theorem root_sixth_rate (q A delta : ℝ) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hdelta : 0 ≤ delta) (hpower : q^6 ≤ A*delta) :
    q ≤ A^((1 : ℝ)/6)*delta^((1 : ℝ)/6) := by
  apply (pow_le_pow_iff_left₀ hq (by positivity) (by norm_num : (6 : ℕ)≠0)).mp
  rwa [mul_pow,root_sixth_power A hA,root_sixth_power delta hdelta]

theorem root_young_mixed (delta m : ℝ) (hdelta : delta ∈ Icc (0 : ℝ) 1) (hm : 0 ≤ m) :
    delta^((1 : ℝ)/8)*m^((3 : ℝ)/8) ≤ delta^((1 : ℝ)/6)+m := by
  have hy := Real.geom_mean_le_arith_mean2_weighted
    (by norm_num : (0 : ℝ)≤5/8) (by norm_num : (0 : ℝ)≤3/8)
    (Real.rpow_nonneg hdelta.1 ((1 : ℝ)/5)) hm (by norm_num : (5/8 : ℝ)+3/8=1)
  rw [←Real.rpow_mul hdelta.1] at hy
  norm_num only [show ((1 : ℝ)/5)*(5/8)=1/8 by norm_num] at hy
  have hp : delta^((1 : ℝ)/5) ≤ delta^((1 : ℝ)/6) :=
    Real.rpow_le_rpow_of_exponent_ge' hdelta.1 hdelta.2 (by norm_num) (by norm_num)
  nlinarith [Real.rpow_nonneg hdelta.1 ((1 : ℝ)/5),Real.rpow_nonneg hdelta.1 ((1 : ℝ)/6)]

theorem root_fourth_mixed_rate (q B C delta m : ℝ) (hq : 0 ≤ q)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hdelta : delta ∈ Icc (0 : ℝ) 1) (hm : 0 ≤ m)
    (hpower : q^4 ≤ B*C*delta+B*delta^((1 : ℝ)/2)*m^((3 : ℝ)/2)) :
    q ≤ max ((2*B*C)^((1 : ℝ)/4)) ((2*B)^((1 : ℝ)/4)) *
      (delta^((1 : ℝ)/6)+m) := by
  have hroot := Real.rpow_nonneg hdelta.1 ((1 : ℝ)/6)
  have hdelta0 : 0 ≤ delta := hdelta.1
  have hsum : 0 ≤ delta^((1 : ℝ)/6)+m := add_nonneg hroot hm
  by_cases hfirst : q^4 ≤ 2*B*C*delta
  · have hqroot : q ≤ (2*B*C)^((1 : ℝ)/4)*delta^((1 : ℝ)/4) := by
      apply (pow_le_pow_iff_left₀ hq (by positivity) (by norm_num : (4 : ℕ)≠0)).mp
      rwa [mul_pow,root_fourth_power (2*B*C) (by positivity),root_fourth_power delta hdelta.1]
    have hp : delta^((1 : ℝ)/4) ≤ delta^((1 : ℝ)/6) :=
      Real.rpow_le_rpow_of_exponent_ge' hdelta.1 hdelta.2 (by norm_num) (by norm_num)
    calc
      q ≤ (2*B*C)^((1 : ℝ)/4)*delta^((1 : ℝ)/4) := hqroot
      _ ≤ (2*B*C)^((1 : ℝ)/4)*(delta^((1 : ℝ)/6)+m) :=
        mul_le_mul_of_nonneg_left (hp.trans (le_add_of_nonneg_right hm)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hsum
  · have hsecond : q^4 ≤ 2*B*delta^((1 : ℝ)/2)*m^((3 : ℝ)/2) := by linarith
    have hqroot : q ≤ (2*B)^((1 : ℝ)/4)*delta^((1 : ℝ)/8)*m^((3 : ℝ)/8) := by
      apply (pow_le_pow_iff_left₀ hq (by positivity) (by norm_num : (4 : ℕ)≠0)).mp
      rw [mul_pow,mul_pow,root_fourth_power (2*B) (by positivity)]
      have hd : (delta^((1 : ℝ)/8))^4=delta^((1 : ℝ)/2) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hdelta.1]
        norm_num
      have hm' : (m^((3 : ℝ)/8))^4=m^((3 : ℝ)/2) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hm]
        norm_num
      rwa [hd,hm']
    calc
      q ≤ (2*B)^((1 : ℝ)/4)*(delta^((1 : ℝ)/8)*m^((3 : ℝ)/8)) := by nlinarith [hqroot]
      _ ≤ (2*B)^((1 : ℝ)/4)*(delta^((1 : ℝ)/6)+m) :=
        mul_le_mul_of_nonneg_left (root_young_mixed delta m hdelta hm) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hsum

theorem root_quantile_reduction (Q T : ℝ) (hQ : Q ∈ Icc (0 : ℝ) 1)
    (hT : T ∈ Ioc (0 : ℝ) 1) : Q ≤ min Q T/T := by
  apply (le_div_iff₀ hT.1).mpr
  by_cases hQT : Q ≤ T
  · rw [min_eq_left hQT]
    nlinarith [hQ.1,hT.2]
  · rw [min_eq_right (le_of_not_ge hQT)]
    nlinarith [hQ.2,hT.1]

theorem root_balance_power_cases (q beta C₄ delta d : ℝ)
    (hq : 0 < q) (hbeta : 0 < beta) (hd : 0 < d)
    (hbalance : min (7*q^3/(3840*beta)) (2*q/(15*d)) ≤ C₄*delta/q^3) :
    q^6 ≤ (3840*beta*C₄/7)*delta ∨ q^4 ≤ (15*C₄/2)*d*delta := by
  rcases min_le_iff.mp hbalance with hfirst|hsecond
  · left
    have hc := (div_le_div_iff₀ (by positivity : 0 < 3840*beta)
      (pow_pos hq 3)).mp hfirst
    nlinarith
  · right
    have hc := (div_le_div_iff₀ (by positivity : 0 < 15*d)
      (pow_pos hq 3)).mp hsecond
    nlinarith

end QuantitativeFollowup
