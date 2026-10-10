module
public import QuantitativePaper.P2SmoothingWidth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Exact power extraction from the sharper midpoint balance. These are
scalar algebraic lemmas; the actual midpoint and minimization budgets are
proved in separate modules before using this extraction. -/
noncomputable section
open Set
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem p2_eta_balance_rate (c r q η : ℝ) (hc : 0 < c) (hr : 0 < r)
    (hq : 0 ≤ q) (hη : 0 ≤ η)
    (h : c*r^3*Real.sqrt r*q^5*Real.sqrt q ≤ 2*η) :
    q ≤ (2/c)^(2/11 : ℝ)*r^(-7/11 : ℝ)*η^(2/11 : ℝ) := by
  have hs := pow_le_pow_left₀ (show 0 ≤ c*r^3*Real.sqrt r*q^5*Real.sqrt q by positivity) h 2
  have he : (c*r^3*Real.sqrt r*q^5*Real.sqrt q)^2 = c^2*r^7*q^11 := by
    simp only [mul_pow,pow_mul,Real.sq_sqrt hr.le,Real.sq_sqrt hq]
    ring
  rw [he] at hs
  have hpower : q^11 ≤ 4*η^2/(c^2*r^7) := by
    apply (le_div_iff₀ (by positivity : 0 < c^2*r^7)).mpr
    nlinarith only [hs]
  apply (pow_le_pow_iff_left₀ hq (by positivity) (by norm_num : (11 : ℕ) ≠ 0)).mp
  rw [mul_pow,mul_pow]
  have h₀ : ((2/c)^(2/11 : ℝ))^11 = (2/c)^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ 2/c)]
    norm_num
  have h₁ : (r^(-7/11 : ℝ))^11 = (r^7)⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    norm_num
  have h₂ : (η^(2/11 : ℝ))^11 = η^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hη]
    norm_num
  rw [h₀,h₁,h₂]
  convert hpower using 1
  field_simp
  ring

theorem p2_mass_balance_rate (c r q m : ℝ) (hc : 0 < c) (hr : 0 < r)
    (hq : 0 < q) (hm : 0 ≤ m)
    (h : c*r^3*Real.sqrt r*q^5*Real.sqrt q ≤ 2*r^2*q^3*m^3) :
    q ≤ (2/c)^(2/5 : ℝ)*r^(-3/5 : ℝ)*m^(6/5 : ℝ) := by
  have hcancel : c*r*Real.sqrt r*q^2*Real.sqrt q ≤ 2*m^3 := by
    apply (mul_le_mul_iff_left₀ (show 0 < r^2*q^3 by positivity)).mp
    convert h using 1 <;> ring
  have hs := pow_le_pow_left₀ (show 0 ≤ c*r*Real.sqrt r*q^2*Real.sqrt q by positivity) hcancel 2
  have he : (c*r*Real.sqrt r*q^2*Real.sqrt q)^2 = c^2*r^3*q^5 := by
    simp only [mul_pow,pow_mul,Real.sq_sqrt hr.le,Real.sq_sqrt hq.le]
    ring
  rw [he] at hs
  have hpower : q^5 ≤ 4*m^6/(c^2*r^3) := by
    apply (le_div_iff₀ (by positivity : 0 < c^2*r^3)).mpr
    nlinarith only [hs]
  apply (pow_le_pow_iff_left₀ hq.le (by positivity) (by norm_num : (5 : ℕ) ≠ 0)).mp
  rw [mul_pow,mul_pow]
  have h₀ : ((2/c)^(2/5 : ℝ))^5 = (2/c)^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ 2/c)]
    norm_num
  have h₁ : (r^(-3/5 : ℝ))^5 = (r^3)⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    norm_num
  have h₂ : (m^(6/5 : ℝ))^5 = m^6 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hm]
    norm_num
  rw [h₀,h₁,h₂]
  convert hpower using 1
  field_simp
  ring

theorem p2_mass_six_fifths_le (m u : ℝ) (hm : 0 ≤ m) (hu : u ∈ Ioc (0 : ℝ) 1)
    (hmu : m ≤ 2*u) : m^(6/5 : ℝ) ≤ 4*u := by
  have hu0 : 0 < u := hu.1
  have h₀ := Real.rpow_le_rpow hm hmu (by norm_num : (0 : ℝ) ≤ 6/5)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.1.le] at h₀
  have h₁ : (2 : ℝ)^(6/5 : ℝ) ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (6/5 : ℝ) ≤ 2)
    norm_num at hh ⊢
    exact hh
  have h₂ : u^(6/5 : ℝ) ≤ u := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hu.1.le hu.2
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 6/5)
  exact h₀.trans (mul_le_mul h₁ h₂ (by positivity) (by norm_num))

theorem p2_midpoint_balance_rate (c r q m u η : ℝ) (hc : 0 < c) (hr : 0 < r)
    (hq : 0 < q) (hm : 0 ≤ m) (hu : u ∈ Ioc (0 : ℝ) 1) (hmu : m ≤ 2*u) (hη : 0 ≤ η)
    (h : c*r^3*Real.sqrt r*q^5*Real.sqrt q ≤ η+r^2*q^3*m^3) :
    q ≤ max ((2/c)^(2/11 : ℝ)) (4*(2/c)^(2/5 : ℝ))*
      (r^(-3/5 : ℝ)*u+r^(-7/11 : ℝ)*η^(2/11 : ℝ)) := by
  have hu0 : 0 < u := hu.1
  have hbase : 0 < 2/c := div_pos (by norm_num) hc
  by_cases hcase : c*r^3*Real.sqrt r*q^5*Real.sqrt q ≤ 2*η
  · have hh := p2_eta_balance_rate c r q η hc hr hq.le hη hcase
    have hb := mul_le_mul_of_nonneg_right (le_max_left ((2/c)^(2/11 : ℝ)) (4*(2/c)^(2/5 : ℝ)))
      (show 0 ≤ r^(-7/11 : ℝ)*η^(2/11 : ℝ) by positivity)
    have hadd : 0 ≤ max ((2/c)^(2/11 : ℝ)) (4*(2/c)^(2/5 : ℝ))*(r^(-3/5 : ℝ)*u) := by positivity
    rw [mul_add]
    nlinarith only [hh,hb,hadd]
  · have hcase' : c*r^3*Real.sqrt r*q^5*Real.sqrt q ≤ 2*r^2*q^3*m^3 := by linarith only [h,hcase]
    have hh := p2_mass_balance_rate c r q m hc hr hq hm hcase'
    have hmass := p2_mass_six_fifths_le m u hm hu hmu
    have hmultiply := mul_le_mul_of_nonneg_left hmass
      (show 0 ≤ (2/c)^(2/5 : ℝ)*r^(-3/5 : ℝ) by positivity)
    have hb := mul_le_mul_of_nonneg_right (le_max_right ((2/c)^(2/11 : ℝ)) (4*(2/c)^(2/5 : ℝ)))
      (show 0 ≤ r^(-3/5 : ℝ)*u by positivity)
    have hadd : 0 ≤ max ((2/c)^(2/11 : ℝ)) (4*(2/c)^(2/5 : ℝ))*(r^(-7/11 : ℝ)*η^(2/11 : ℝ)) := by positivity
    rw [mul_add]
    nlinarith only [hh,hmultiply,hb,hadd]

end QuantitativePaper
