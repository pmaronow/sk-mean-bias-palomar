module
public import QuantitativeFollowup.NativeCenteredEnergyPositiveBounds
public import QuantitativeFollowup.NativeCenteredFreeEnergy

@[expose] public section

/-! The actual centered free energy inherits the proved global positive
CGF estimate with its correct temperature scaling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem improved_centered_free_energy_positive_cgf_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤C*fourTermBudgetRate (n:ℝ) lam) :
    ∃K : ℝ,∃N0 : ℕ,0<K ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n → ∀s : ℝ,0<s →
      centeredFreeEnergyCGF n β s≤K*((n:ℝ)^(11/25:ℝ)*s^2+(n:ℝ)*s^6) := by
  obtain ⟨Ke,N0,hKe,hN0,hEnergy⟩:=
    improved_centered_energy_positive_cgf_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  let K:=Ke*(β^2+β^6)
  have hβp : 0<β:=zero_lt_one.trans hβ
  have hK : 0<K:=mul_pos hKe (add_pos (sq_pos_of_pos hβp) (pow_pos hβp 6))
  have hK2 : Ke*β^2≤K:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
    (pow_nonneg hβp.le 6)) hKe.le
  have hK6 : Ke*β^6≤K:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left
    (sq_nonneg β)) hKe.le
  refine ⟨K,N0,hK,hN0,?_⟩
  intro n hn s hs
  rw [centeredFreeEnergyCGF_eq_energy n β s hβp.ne']
  have hb:=hEnergy n hn (β*s) (mul_pos hβp hs)
  calc
    _≤Ke*((n:ℝ)^(11/25:ℝ)*(β*s)^2+(n:ℝ)*(β*s)^6):=hb
    _=(Ke*β^2)*((n:ℝ)^(11/25:ℝ)*s^2)+(Ke*β^6)*((n:ℝ)*s^6):=by ring
    _≤K*((n:ℝ)^(11/25:ℝ)*s^2)+K*((n:ℝ)*s^6):=add_le_add
      (mul_le_mul_of_nonneg_right hK2 (by positivity))
      (mul_le_mul_of_nonneg_right hK6 (by positivity))
    _=_:=by ring

end QuantitativeFollowup
