module
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-! The exact real powers used in the last step of the absolute comparison.
These algebraic estimates have no stochastic or variational premises. -/
noncomputable section
namespace QuantitativePaper
set_option maxHeartbeats 500000

theorem absoluteComparison_monomial_rpow (N l a b p : ℝ) (hN : 0≤N) (hl : 0≤l) :
    (N^a*l^b)^p=N^(a*p)*l^(b*p) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hN _) (Real.rpow_nonneg hl _),
    ←Real.rpow_mul hN,←Real.rpow_mul hl]

theorem absoluteComparison_power_identity (N l : ℝ) (hN : 0<N) (hl : 0<l) :
    (N^(-(2:ℝ)/3)*l^(-(1:ℝ)/3))^((12:ℝ)/11)=
      (N^(-(2:ℝ)/3))^((3:ℝ)/11)*
        (N^(-(3:ℝ)/4)*l^(-(1:ℝ)/2))^((8:ℝ)/11) := by
  rw [absoluteComparison_monomial_rpow N l _ _ _ hN.le hl.le,
    absoluteComparison_monomial_rpow N l _ _ _ hN.le hl.le,
    ←Real.rpow_mul hN.le]
  rw [←mul_assoc,←Real.rpow_add hN]
  congr 1 <;> congr 1 <;> norm_num

theorem absoluteComparison_power_le (N l : ℝ) (hN : 0<N) (hl : 0<l) :
    (N^(-(2:ℝ)/3)*l^(-(1:ℝ)/3))^((12:ℝ)/11)≤
      N^(-(2:ℝ)/3)+N^(-(3:ℝ)/4)*l^(-(1:ℝ)/2) := by
  rw [absoluteComparison_power_identity N l hN hl]
  have ha:=Real.rpow_nonneg hN.le (-(2:ℝ)/3)
  have hb:=mul_nonneg (Real.rpow_nonneg hN.le (-(3:ℝ)/4))
    (Real.rpow_nonneg hl.le (-(1:ℝ)/2))
  have h:=Real.geom_mean_le_arith_mean2_weighted
    (show 0≤(3:ℝ)/11 by norm_num) (show 0≤(8:ℝ)/11 by norm_num) ha hb (by norm_num)
  exact h.trans (by nlinarith)

theorem absoluteComparison_trial_power_le (N l : ℝ) (hN : 0<N) (hl : 0<l) (hl1 : l≤1) :
    (N^(-(2:ℝ)/3)*l^(-(1:ℝ)/3))*(l^5)^((1:ℝ)/11)≤N^(-(2:ℝ)/3) := by
  have hp : (l^5)^((1:ℝ)/11)=l^((5:ℝ)/11) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hl.le]
    norm_num
  rw [hp,mul_assoc,←Real.rpow_add hl]
  have he : -(1:ℝ)/3+(5:ℝ)/11=(4:ℝ)/33 := by norm_num
  rw [he]
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_one hl.le hl1 (by norm_num))
    (Real.rpow_nonneg hN.le _)).trans_eq (mul_one _)

end QuantitativePaper
