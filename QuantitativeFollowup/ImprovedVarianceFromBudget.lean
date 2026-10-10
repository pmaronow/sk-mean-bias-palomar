module
public import QuantitativeFollowup.ImprovedMeanBiasFromBudget
public import QuantitativeFollowup.ImprovedFluctuationPowerCalculus
public import QuantitativePaper.ShortVarianceMeanProposition
public import QuantitativePaper.MainFluctuationTargets

@[expose] public section

/-! The actual five-fourths mean/variance inequality yields the printed
11/25 upper power from the native four-term budget. The 9/10 lower mean
power is derived from the separate genuine 7/25 lower variance bound. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000

theorem improved_energy_variance_upper_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0 ≤ C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2 ≤ n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam ≤ C*fourTermBudgetRate (n:ℝ) lam) :
    ∃Cv : ℝ,0<Cv ∧ ∀n : ℕ,2 ≤ n →
      variance (energyFreeEnergy n β) (couplingLaw n) ≤ Cv*(n:ℝ)^(11/25:ℝ) := by
  obtain ⟨Cm,hCm,hMean⟩:=improved_energy_mean_bias_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  obtain ⟨cs,hcs,hShort⟩:=short_variance_mean β hβ
  refine ⟨(Cm/cs)^(4/5:ℝ),Real.rpow_pos_of_pos (div_pos hCm hcs) _,?_⟩
  intro n hn
  have hn0 : 0<n:=by omega
  have hh:=variance_upper_of_mean_exponent (n:ℝ)
    (variance (energyFreeEnergy n β) (couplingLaw n)) (energyMeanDeficit n β) cs Cm (7/10:ℝ)
    (Nat.cast_pos.mpr hn0) (variance_nonneg _ _) hcs hCm (hShort n hn0 β le_rfl) (hMean n hn).2
  norm_num only [show (1:ℝ)-(4/5:ℝ)*(7/10:ℝ)=11/25 by norm_num] at hh
  exact hh

theorem improved_native_variance_upper_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0 ≤ C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2 ≤ n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam ≤ C*fourTermBudgetRate (n:ℝ) lam) :
    ∃Cv : ℝ,0<Cv ∧ ∀n : ℕ,2 ≤ n → freeEnergyVariance n β ≤ Cv*(n:ℝ)^(11/25:ℝ) := by
  obtain ⟨Cv,hCv,hVar⟩:=improved_energy_variance_upper_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  have hβp : 0<β:=zero_lt_one.trans hβ
  refine ⟨β^2*Cv,mul_pos (sq_pos_of_pos hβp) hCv,?_⟩
  intro n hn
  rw [freeEnergyVariance_eq_scaled_energyVariance n β hβp.ne']
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hVar n hn) (sq_nonneg β)

theorem improved_energy_mean_lower_of_variance_lower (β : ℝ) (hβ : 1<β)
    (k : ℝ) (hk : 0<k) :
    ∃c : ℝ,0<c ∧ ∀n : ℕ,0<n →
      k*(n:ℝ)^(7/25:ℝ) ≤ variance (energyFreeEnergy n β) (couplingLaw n) →
      c*(n:ℝ)^(-(9/10:ℝ)) ≤ energyMeanDeficit n β := by
  obtain ⟨cs,hcs,hShort⟩:=short_variance_mean β hβ
  refine ⟨cs*k^(5/4:ℝ),mul_pos hcs (Real.rpow_pos_of_pos hk _),?_⟩
  intro n hn hVar
  have hh:=mean_lower_of_variance_exponent (n:ℝ)
    (variance (energyFreeEnergy n β) (couplingLaw n)) (energyMeanDeficit n β) cs k (7/25:ℝ)
    (Nat.cast_pos.mpr hn) hcs.le hk hVar (hShort n hn β le_rfl)
  norm_num only [show ((7/25:ℝ)-1)*(5/4:ℝ)=-(9/10:ℝ) by norm_num] at hh
  exact hh

end QuantitativeFollowup
