module
public import QuantitativeFollowup.RootRateArithmetic

@[expose] public section

/-! The zero-trial-budget limit in root localization, proved without
division by the budget or an assumed continuity of model minimizers. -/
noncomputable section
namespace QuantitativeFollowup

theorem root_zero_budget_limit (Q C lam v rho : ℝ) (hC : 0 < C) (hrho : 0 < rho)
    (hBound : ∀eta : ℝ, 0 < eta →
      Q ≤ C*(lam+v+min 1 ((eta/rho)^((1 : ℝ)/6)))) :
    Q ≤ C*(lam+v) := by
  apply le_of_forall_pos_le_add
  intro eps heps
  have hRatio : 0 < eps/C := div_pos heps hC
  let eta := rho*(eps/C)^6
  have heta : 0 < eta := mul_pos hrho (pow_pos hRatio 6)
  have hScale : eta/rho=(eps/C)^6 := by dsimp only [eta]; field_simp
  have hRoot : (eta/rho)^((1 : ℝ)/6)=eps/C := by
    rw [hScale]
    convert Real.pow_rpow_inv_natCast hRatio.le (by norm_num : (6 : ℕ)≠0) using 1 <;> norm_num
  have hSmall := mul_le_mul_of_nonneg_left (min_le_right 1 ((eta/rho)^((1 : ℝ)/6))) hC.le
  have hActual := hBound eta heta
  rw [hRoot] at hActual hSmall
  have hTerm : C*(eps/C)=eps := by field_simp
  rw [hTerm] at hSmall
  nlinarith

end QuantitativeFollowup
