module
public import QuantitativeFollowup.SixthWindowFromBudget
public import QuantitativeFollowup.ImprovedVarianceLowerFromWindow
public import QuantitativeFollowup.ImprovedVarianceFromBudget

@[expose] public section

/-! The actual four-term error budget implies the genuine improved native
lower variance and mean powers. The cavity backend remains explicit. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

theorem improved_energy_variance_lower_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤C*fourTermBudgetRate (n:ℝ) lam) :
    ∃cv : ℝ,∃N0 : ℕ,0<cv ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n →
      cv*(n:ℝ)^(7/25:ℝ)≤variance (energyFreeEnergy n β) (couplingLaw n) := by
  obtain ⟨a,Ls,A,L,Nw,ha,_,hA,hL,_,_,_,_,hLower⟩:=
    improved_sixth_window_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  exact improved_energy_variance_lower_of_sixth_window β (zero_lt_one.trans hβ)
    a A L ha (zero_lt_one.trans_le hA) hL Nw hLower

theorem improved_native_lower_powers_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤C*fourTermBudgetRate (n:ℝ) lam) :
    ∃cv cm : ℝ,∃N0 : ℕ,0<cv ∧ 0<cm ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n →
      cv*(n:ℝ)^(7/25:ℝ)≤freeEnergyVariance n β ∧
      cm*(n:ℝ)^(-(9/10:ℝ))≤finiteBias n β := by
  obtain ⟨cv,N0,hcv,hN0,hVar⟩:=
    improved_energy_variance_lower_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  obtain ⟨cm,hcm,hMean⟩:=improved_energy_mean_lower_of_variance_lower β hβ cv hcv
  have hβp : 0<β:=zero_lt_one.trans hβ
  refine ⟨β^2*cv,β*cm,N0,by positivity,by positivity,hN0,?_⟩
  intro n hn
  have hn0 : 0<n:=by omega
  have hm:=hMean n hn0 (hVar n hn)
  have he : finiteBias n β=β*energyMeanDeficit n β:=by
    rw [energyMeanDeficit_eq_pressure_gap]
    unfold finiteBias parisiLimit
    field_simp
  rw [freeEnergyVariance_eq_scaled_energyVariance n β hβp.ne',he]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hVar n hn) (sq_nonneg β)
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm hβp.le

end QuantitativeFollowup
