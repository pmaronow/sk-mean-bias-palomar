module
public import QuantitativeFollowup.ImprovedMatchingTailsFromBudget
public import QuantitativeFollowup.ImprovedVarianceLowerFromBudget

@[expose] public section

/-! All literal fixed-temperature improved fluctuation clauses are assembled
from the actual four-term budget. Its cavity proof is an explicit input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem improved_native_fluctuations_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤C*fourTermBudgetRate (n:ℝ) lam) :
    ∃c Cf A xβ : ℝ,0<c ∧ 0<Cf ∧ 0<A ∧ 0<xβ ∧ ∃N0 : ℕ,
      (∀n : ℕ,2≤n → freeEnergyVariance n β≤Cf*(n:ℝ)^(11/25:ℝ)) ∧
      (∀n : ℕ,N0≤n → c*(n:ℝ)^(7/25:ℝ)≤freeEnergyVariance n β ∧
        c*(n:ℝ)^(-(9/10:ℝ))≤finiteBias n β ∧
        ∀x : ℝ,A*(n:ℝ)^(-(7/10:ℝ))≤x → x≤xβ →
          Real.exp (-Cf*(n:ℝ)*x^(6/5:ℝ))≤
            (couplingLaw n).real {g | (n:ℝ)*(parisiLimit β+x)≤logPartition n β g} ∧
          (couplingLaw n).real {g | (n:ℝ)*(parisiLimit β+x)≤logPartition n β g}≤
            Real.exp (-c*(n:ℝ)*x^(6/5:ℝ))) := by
  obtain ⟨Cv,hCv,hVarUpper⟩:=
    improved_native_variance_upper_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  obtain ⟨cv,cm,Nv,hcv,hcm,hNv,hLower⟩:=
    improved_native_lower_powers_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  obtain ⟨A,xβ,ct,Ct,Nt,hA,hxβ,hct,hCt,hNt,hTails⟩:=
    improved_native_matching_tails_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  let c:=min cv (min cm ct)
  let Cf:=max Cv Ct
  have hc : 0<c:=lt_min hcv (lt_min hcm hct)
  have hCf : 0<Cf:=hCv.trans_le (le_max_left _ _)
  refine ⟨c,Cf,A,xβ,hc,hCf,hA,hxβ,max Nv Nt,?_,?_⟩
  · intro n hn
    exact (hVarUpper n hn).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · intro n hn
    have hnv : Nv≤n:=(le_max_left _ _).trans hn
    have hnt : Nt≤n:=(le_max_right _ _).trans hn
    have hv:=hLower n hnv
    refine ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans hv.1,
      (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans hv.2,?_⟩
    intro x hxLow hxHigh
    have hx : 0≤x:=(mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans hxLow
    have ht:=hTails n hnt x hxLow hxHigh
    constructor
    · apply le_trans (Real.exp_le_exp.mpr ?_) ht.1
      have hh:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right Cv Ct) (Nat.cast_nonneg n))
        (Real.rpow_nonneg hx (6/5:ℝ))
      dsimp only [Cf]
      linarith
    · apply ht.2.trans (Real.exp_le_exp.mpr ?_)
      have hctc : c≤ct:=(min_le_right _ _).trans (min_le_right _ _)
      have hh:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hctc (Nat.cast_nonneg n))
        (Real.rpow_nonneg hx (6/5:ℝ))
      linarith

end QuantitativeFollowup
