module
public import QuantitativeFollowup.ImprovedFreeEnergyPositiveCGF
public import QuantitativeFollowup.ImprovedVarianceFromBudget
public import QuantitativeFollowup.NativeNegativeFractionalGap
public import QuantitativeFollowup.ImprovedVarianceDensityPower
public import FourPapersCommon.TwoScaleChernoff

@[expose] public section

/-! Literal improved mean-centered concentration and negative fractional
pressure follow from the genuine native error budget, without assuming
any concentration result. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

theorem improved_native_concentration_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤ C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤ n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤ C*fourTermBudgetRate (n:ℝ) lam) :
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
  obtain ⟨K,N0,hK,hN0,hPositive⟩:=
    improved_centered_free_energy_positive_cgf_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  obtain ⟨Cv,hCv,hVar⟩:=
    improved_native_variance_upper_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  obtain ⟨Cm,hCm,hMean⟩:=improved_native_bias_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  let cn:=1/(2*Cv)
  let cp:=min (1/(8*K)) (1/(2*(4*K)^(1/5:ℝ)))
  let c:=min cn cp
  let Cc:=max Cm (Cv/2)
  have hcn : 0<cn:=by dsimp only [cn];positivity
  have hcp : 0<cp:=lt_min (by positivity) (by positivity)
  have hc : 0<c:=lt_min hcn hcp
  have hCc : 0<Cc:=hCm.trans_le (le_max_left _ _)
  have hβp : 0<β:=zero_lt_one.trans hβ
  refine ⟨c,Cc,N0,hc,hCc,hN0,?_⟩
  intro n hn
  have hn2 : 2≤ n:=hN0.trans hn
  have hn0 : 0<n:=by omega
  have hNp : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
  let Q:=(n:ℝ)^(11/25:ℝ)
  have hQ : 0<Q:=Real.rpow_pos_of_pos hNp _
  have hNegative (s : ℝ) (hs : s<0) :
      centeredFreeEnergyCGF n β s≤(Cv/2*Q)*s^2:=by
    have hh:=native_centered_free_energy_cgf_negative_variance_bound n β hβp s hs
    have hv:=mul_le_mul_of_nonneg_left (hVar n hn2) (by positivity : 0≤ s^2/2)
    exact hh.trans (by convert hv using 1 <;> ring)
  constructor
  · intro u hu
    have hLower:=lower_tail_of_negative_cgf_quadratic (couplingLaw n)
      (centeredFreeEnergyVariable n β) (Cv/2*Q) (by positivity)
      (fun s _=>integrable_exp_centeredFreeEnergy n β s) hNegative u hu
    have hUpper:=upper_tail_of_cgf_quadratic_sixth (couplingLaw n)
      (centeredFreeEnergyVariable n β) K Q (n:ℝ) hK hQ hNp
      (fun s _=>integrable_exp_centeredFreeEnergy n β s) (hPositive n hn) u hu
    have he : -u^2/(4*(Cv/2*Q))=-cn*(u^2/Q):=by
      dsimp only [cn]
      field_simp [hCv.ne',hQ.ne']
      <;> ring
    rw [he] at hLower
    constructor
    · apply hLower.trans (Real.exp_le_exp.mpr ?_)
      have hh:=mul_le_mul_of_nonneg_right (min_le_left cn cp) (by positivity : 0≤ u^2/Q)
      dsimp only [c,Q]
      dsimp only [Q] at hh
      linarith
    · apply hUpper.trans (Real.exp_le_exp.mpr ?_)
      have hh:=mul_le_mul_of_nonneg_right (min_le_right cn cp)
        (show 0≤ min (u^2/Q) (u^(6/5:ℝ)/(n:ℝ)^(1/5:ℝ)) by
          apply le_min <;> positivity)
      dsimp only [c,cp,Q] at hh ⊢
      linarith
  · intro s hs
    have hGap:=native_negative_fractional_gap_bounds n hn0 β hβp s hs
    refine ⟨hGap.1,?_⟩
    have hMul:=mul_le_mul_of_nonneg_left (hVar n hn2)
      (by positivity : 0≤|s|/(2*(n:ℝ)))
    have he : |s|/(2*(n:ℝ))*(Cv*(n:ℝ)^(11/25:ℝ))=
        Cv/2*(|s| *(n:ℝ)^(-(14/25:ℝ))):=by
      rw [←improved_variance_density_power (n:ℝ) hNp]
      ring
    rw [he] at hMul
    have hFirst:=mul_le_mul_of_nonneg_right (le_max_left Cm (Cv/2))
      (Real.rpow_nonneg hNp.le (-(7/10:ℝ)))
    have hSecond:=mul_le_mul_of_nonneg_right (le_max_right Cm (Cv/2))
      (show 0≤|s| *(n:ℝ)^(-(14/25:ℝ)) by positivity)
    dsimp only [Cc]
    nlinarith only [hGap.2,(hMean n hn2).2,hMul,hFirst,hSecond]

end QuantitativeFollowup
