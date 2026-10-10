module
public import QuantitativeFollowup.FollowupCavityActualStableProfile
public import QuantitativeFollowup.ImprovedMeanBiasFromBudget
public import QuantitativeFollowup.ImprovedVarianceFromBudget
public import QuantitativeFollowup.ImprovedVarianceLowerFromBudget
public import QuantitativeFollowup.ImprovedMatchingTailsFromBudget
public import QuantitativeFollowup.ImprovedFluctuationFromBudget
public import QuantitativeFollowup.ImprovedConcentrationFromBudget
public import QuantitativeFollowup.SixthWindowFromBudget

@[expose] public section

/-! Native main consequences with the proved four-term budget discharged. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem improved_native_bias (β : ℝ) (hβ : 1<β) :
    ∃Cm : ℝ,0<Cm ∧ ∀n : ℕ,2 ≤ n →
      0 ≤ finiteBias n β ∧ finiteBias n β ≤ Cm*(n:ℝ)^(-(7/10:ℝ)) := by
  obtain ⟨C,L,lambda0,hC,hL,h0,h0β,hBudget⟩ := followup_actual_four_term_budget β hβ
  exact improved_native_bias_of_four_term_budget β hβ C lambda0 hC.le h0
    (fun n hn lam hlam => (hBudget n hn lam hlam).2)

theorem improved_native_variance_upper (β : ℝ) (hβ : 1<β) :
    ∃Cv : ℝ,0<Cv ∧ ∀n : ℕ,2 ≤ n → freeEnergyVariance n β ≤ Cv*(n:ℝ)^(11/25:ℝ) := by
  obtain ⟨C,L,lambda0,hC,hL,h0,h0β,hBudget⟩ := followup_actual_four_term_budget β hβ
  exact improved_native_variance_upper_of_four_term_budget β hβ C lambda0 hC.le h0
    (fun n hn lam hlam => (hBudget n hn lam hlam).2)

theorem improved_native_lower_powers (β : ℝ) (hβ : 1<β) :
    ∃cv cm : ℝ,∃N0 : ℕ,0<cv ∧ 0<cm ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n →
      cv*(n:ℝ)^(7/25:ℝ)≤freeEnergyVariance n β ∧
      cm*(n:ℝ)^(-(9/10:ℝ))≤finiteBias n β := by
  obtain ⟨C,L,lambda0,hC,hL,h0,h0β,hBudget⟩ := followup_actual_four_term_budget β hβ
  exact improved_native_lower_powers_of_four_term_budget β hβ C lambda0 hC.le h0
    (fun n hn lam hlam => (hBudget n hn lam hlam).2)

theorem improved_native_matching_tails (β : ℝ) (hβ : 1<β) :
    ∃Ao xo co Co : ℝ,∃N0 : ℕ,
      0<Ao ∧ 0<xo ∧ 0<co ∧ 0<Co ∧ 2≤N0 ∧ ∀n : ℕ,N0≤n →
      ∀x : ℝ,Ao*(n:ℝ)^(-(7/10:ℝ))≤x → x≤xo →
        Real.exp (-Co*(n:ℝ)*x^(6/5:ℝ))≤
          (couplingLaw n).real {g | (n:ℝ)*(Paper.parisiPDEValue β 0+x)≤logPartition n β g} ∧
        (couplingLaw n).real {g | (n:ℝ)*(Paper.parisiPDEValue β 0+x)≤logPartition n β g}≤
          Real.exp (-co*(n:ℝ)*x^(6/5:ℝ)) := by
  obtain ⟨C,L,lambda0,hC,hL,h0,h0β,hBudget⟩ := followup_actual_four_term_budget β hβ
  exact improved_native_matching_tails_of_four_term_budget β hβ C lambda0 hC.le h0
    (fun n hn lam hlam => (hBudget n hn lam hlam).2)

theorem improved_native_fluctuations (β : ℝ) (hβ : 1<β) :
    ∃c Cf A xβ : ℝ,0<c ∧ 0<Cf ∧ 0<A ∧ 0<xβ ∧ ∃N0 : ℕ,
      (∀n : ℕ,2≤n → freeEnergyVariance n β≤Cf*(n:ℝ)^(11/25:ℝ)) ∧
      (∀n : ℕ,N0≤n → c*(n:ℝ)^(7/25:ℝ)≤freeEnergyVariance n β ∧
        c*(n:ℝ)^(-(9/10:ℝ))≤finiteBias n β ∧
        ∀x : ℝ,A*(n:ℝ)^(-(7/10:ℝ))≤x → x≤xβ →
          Real.exp (-Cf*(n:ℝ)*x^(6/5:ℝ))≤
            (couplingLaw n).real {g | (n:ℝ)*(parisiLimit β+x)≤logPartition n β g} ∧
          (couplingLaw n).real {g | (n:ℝ)*(parisiLimit β+x)≤logPartition n β g}≤
            Real.exp (-c*(n:ℝ)*x^(6/5:ℝ))) := by
  obtain ⟨C,L,lambda0,hC,hL,h0,h0β,hBudget⟩ := followup_actual_four_term_budget β hβ
  exact improved_native_fluctuations_of_four_term_budget β hβ C lambda0 hC.le h0
    (fun n hn lam hlam => (hBudget n hn lam hlam).2)

theorem improved_native_concentration (β : ℝ) (hβ : 1<β) :
    ∃c Cc : ℝ,∃N0 : ℕ,0<c ∧ 0<Cc ∧ 2≤ N0 ∧ ∀n : ℕ,N0≤ n →
      (∀u : ℝ,0≤ u →
        (couplingLaw n).real {g | centeredFreeEnergyVariable n β g≤-u}≤
          Real.exp (-c*(u^2/(n:ℝ)^(11/25:ℝ))) ∧
        (couplingLaw n).real {g | u≤ centeredFreeEnergyVariable n β g}≤
          Real.exp (-c*min (u^2/(n:ℝ)^(11/25:ℝ)) (u^(6/5:ℝ)/(n:ℝ)^(1/5:ℝ)))) ∧
      (∀s : ℝ,s<0 →
        0≤ parisiLimit β-cgf (logPartition n β) (couplingLaw n) s/((n:ℝ)*s) ∧
        parisiLimit β-cgf (logPartition n β) (couplingLaw n) s/((n:ℝ)*s)≤
          Cc*((n:ℝ)^(-(7/10:ℝ))+|s| *(n:ℝ)^(-(14/25:ℝ)))) := by
  obtain ⟨C,L,lambda0,hC,hL,h0,h0β,hBudget⟩ := followup_actual_four_term_budget β hβ
  exact improved_native_concentration_of_four_term_budget β hβ C lambda0 hC.le h0
    (fun n hn lam hlam => (hBudget n hn lam hlam).2)

theorem improved_sixth_window (β : ℝ) (hβ : 1<β) :
    ∃a Ls A L : ℝ,∃N0 : ℕ,0<a ∧ 1≤Ls ∧ 1≤A ∧
      0<L ∧ L≤1 ∧ L≤β/2 ∧ 2≤N0 ∧
      (∀n : ℕ,2≤n → ∀lam∈Ioc (0:ℝ) L,
        scalarCenteredEnergyLogMoment n β lam≤Ls*(n:ℝ)*lam^6) ∧
      (∀n : ℕ,N0≤n → ∀lam : ℝ,A*(n:ℝ)^(-(7/50:ℝ))≤lam → lam≤L →
        a*(n:ℝ)*lam^6≤ scalarCenteredEnergyLogMoment n β lam) := by
  obtain ⟨C,L,lambda0,hC,hL,h0,h0β,hBudget⟩ := followup_actual_four_term_budget β hβ
  exact improved_sixth_window_of_four_term_budget β hβ C lambda0 hC.le h0
    (fun n hn lam hlam => (hBudget n hn lam hlam).2)

theorem followup_bias_target : BiasTarget := by
  intro β hβ
  obtain ⟨C,hC,hAll⟩ := improved_native_bias β hβ
  exact ⟨C,hC.le,hAll⟩

theorem followup_fluctuation_target : FluctuationTarget := by
  intro β hβ
  simpa only [Measure.real] using improved_native_fluctuations β hβ

end QuantitativeFollowup
