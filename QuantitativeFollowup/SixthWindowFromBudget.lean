module
public import QuantitativeFollowup.FourTermWindowAsymptotics
public import QuantitativePaper.ScalarFisherLowerProposition
public import QuantitativePaper.SixthWindowEnergy

@[expose] public section

/-! The genuine improved sixth-power window follows from the separately
stated native four-term error budget. No cumulant lower bound is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem improved_sixth_window_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0≤C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2≤n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam≤C*fourTermBudgetRate (n:ℝ) lam) :
    ∃a Ls A L : ℝ,∃N0 : ℕ,0<a ∧ 1≤Ls ∧ 1≤A ∧
      0<L ∧ L≤1 ∧ L≤β/2 ∧ 2≤N0 ∧
      (∀n : ℕ,2≤n → ∀lam∈Ioc (0:ℝ) L,
        scalarCenteredEnergyLogMoment n β lam≤Ls*(n:ℝ)*lam^6) ∧
      (∀n : ℕ,N0≤n → ∀lam : ℝ,A*(n:ℝ)^(-(7/50:ℝ))≤lam → lam≤L →
        a*(n:ℝ)*lam^6≤ scalarCenteredEnergyLogMoment n β lam) := by
  obtain ⟨c,Ls,Lcost,hc,hLs,hLcost,hLcost1,hLcostβ,hCost⟩:=scalar_fisher_lower β hβ
  let L:=min Lcost lambda0
  have hL : 0<L:=lt_min hLcost h0.1
  have hL1 : L≤1:=(min_le_left _ _).trans hLcost1
  have hLβ : L≤β/2:=(min_le_left _ _).trans hLcostβ
  obtain ⟨A,hA,N0,hN0,hSmall⟩:=exists_fourTerm_window_error_cutoff c C hc
  have hAp : 0<A:=zero_lt_one.trans_le hA
  have hβp : 0<β:=zero_lt_one.trans hβ
  refine ⟨c/2,Ls,A,L,N0,by positivity,hLs,hA,hL,hL1,hLβ,hN0,?_,?_⟩
  · intro n hn lam hlam
    have hn0 : 0<n:=by omega
    have hcost:=(hCost β le_rfl lam ⟨hlam.1,hlam.2.trans (min_le_left _ _)⟩).2
    have hRatio : lam/β∈Ioo (0:ℝ) 1:=by
      refine ⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr ?_⟩
      linarith [hlam.2.trans hLβ]
    exact energy_sixth_moment_upper n hn0 β hβp lam Ls hlam.1 hRatio hcost
  · intro n hn lam hWin hUpper
    have hn2 : 2≤n:=hN0.trans hn
    have hn0 : 0<n:=by omega
    have hN : (2:ℝ)≤n:=by exact_mod_cast hn2
    have hNp : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
    have hlam : 0<lam:=(mul_pos hAp (Real.rpow_pos_of_pos hNp _)).trans_le hWin
    have hOpt:=fourTermBudget_optimal_tilt_range (n:ℝ) (by linarith)
    have hScale : (n:ℝ)^(-(7/50:ℝ))≤A*(n:ℝ)^(-(7/50:ℝ)):=by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA
        (Real.rpow_nonneg hNp.le (-(7/50:ℝ)))
    have hInv : (n:ℝ)⁻¹≤lam:=hOpt.1.1.trans (hScale.trans hWin)
    have he:=fourTermBudget_error_window (n:ℝ) A lam (energyComparisonError n β lam) C
      hN hA hC hWin (hBudget n hn2 lam ⟨hInv,hUpper.trans (min_le_right _ _)⟩)
    have hErr : energyComparisonError n β lam≤c/4*lam^5:=
      (div_le_iff₀ (pow_pos hlam 5)).mp (he.trans (hSmall n hn).1)
    have hDiag := (fourTermBudget_window_quadratic_correction (n:ℝ) A lam hNp hAp hWin).trans
      (hSmall n hn).2
    have hd : lam^2/4≤c/4*(n:ℝ)*lam^6:=by
      have hh:=(div_le_iff₀ (mul_pos (mul_pos (by norm_num : 0<(4:ℝ)) hNp)
        (pow_pos hlam 6))).mp hDiag
      nlinarith
    exact energy_sixth_moment_lower n hn0 β lam c hlam
      (hCost β le_rfl lam ⟨hlam,hUpper.trans (min_le_left _ _)⟩).1 hErr hd

end QuantitativeFollowup
