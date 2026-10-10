module
public import QuantitativeFollowup.FourTermBudgetOptimalBound
public import QuantitativeFollowup.FoundationMeanBias
public import QuantitativeFollowup.Targets
public import FourPapersCommon.EventuallyPowerBound

@[expose] public section

/-! Genuine mean-bias consequences of the separate four-term native error
estimate. The remaining error theorem is explicit here; the midpoint
identity, optimal tilt, and finite-size extension are proved model inputs. -/
noncomputable section
open Set Filter MeasureTheory QuantitativePaper FourPapersCommon
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem improved_energy_mean_bias_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0 ≤ C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2 ≤ n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam ≤ C*fourTermBudgetRate (n:ℝ) lam) :
    ∃Cm : ℝ,0<Cm ∧ ∀n : ℕ,2 ≤ n →
      0 ≤ energyMeanDeficit n β ∧ energyMeanDeficit n β ≤ Cm*(n:ℝ)^(-(7/10:ℝ)) := by
  obtain ⟨L,lambdaMean,hL,hMean0,hMeanβ,hMean⟩:=foundation_mean_bias β hβ
  have hβp : 0<β:=zero_lt_one.trans hβ
  have hlim : Tendsto (fun n : ℕ=>(n:ℝ)^(-(7/50:ℝ))) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/50)).comp tendsto_natCast_atTop_atTop
  have hsmall:=hlim.eventually_le_const (lt_min h0.1 hMean0.1)
  let K:=32*L+2*C*(3+(Real.log 2+50)^3)
  have hEvent : ∀ᶠn : ℕ in atTop,energyMeanDeficit n β ≤ K*(n:ℝ)^(-(7/10:ℝ)):=by
    filter_upwards [hsmall,eventually_ge_atTop (2:ℕ)] with n hnSmall hn
    have hn0 : 0<n:=by omega
    have hN : (2:ℝ) ≤ n:=by exact_mod_cast hn
    have hNp : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
    have hopt:=fourTermBudget_optimal_tilt_range (n:ℝ) (by linarith)
    have hlam : (n:ℝ)^(-(7/50:ℝ))∈Icc ((n:ℝ)⁻¹) lambda0:=
      ⟨hopt.1.1,hnSmall.trans (min_le_left _ _)⟩
    have hMeanLam : (n:ℝ)^(-(7/50:ℝ))∈Ioc (0:ℝ) lambdaMean:=
      ⟨hopt.2,hnSmall.trans (min_le_right _ _)⟩
    have he:=hBudget n hn _ hlam
    have hr:=mul_le_mul_of_nonneg_left (fourTermBudgetRate_optimal_bound (n:ℝ) hN) hC
    have hm:=(hMean n hn0 _ hMeanLam).2.1.trans (hMean n hn0 _ hMeanLam).2.2
    rw [fourTermBudget_optimal_trial_power (n:ℝ) hNp.le] at hm
    dsimp only [K]
    nlinarith only [hm,he,hr]
  obtain ⟨Cm,hCm,hAll⟩:=exists_global_nat_power_bound_of_eventually
    (fun n=>energyMeanDeficit n β) (-(7/10:ℝ)) K hEvent
  exact ⟨Cm,hCm,fun n hn=>⟨energyMeanDeficit_nonneg n (by omega) β hβp,hAll n (by omega)⟩⟩

theorem improved_native_bias_of_four_term_budget (β : ℝ) (hβ : 1<β)
    (C lambda0 : ℝ) (hC : 0 ≤ C) (h0 : lambda0∈Ioc (0:ℝ) 1)
    (hBudget : ∀n : ℕ,2 ≤ n → ∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      energyComparisonError n β lam ≤ C*fourTermBudgetRate (n:ℝ) lam) :
    ∃Cm : ℝ,0<Cm ∧ ∀n : ℕ,2 ≤ n →
      0 ≤ finiteBias n β ∧ finiteBias n β ≤ Cm*(n:ℝ)^(-(7/10:ℝ)) := by
  obtain ⟨Cm,hCm,hAll⟩:=improved_energy_mean_bias_of_four_term_budget β hβ C lambda0 hC h0 hBudget
  have hβp : 0<β:=zero_lt_one.trans hβ
  refine ⟨β*Cm,mul_pos hβp hCm,?_⟩
  intro n hn
  have he : finiteBias n β=β*energyMeanDeficit n β:=by
    rw [energyMeanDeficit_eq_pressure_gap]
    unfold finiteBias parisiLimit
    field_simp
  rw [he]
  exact ⟨mul_nonneg hβp.le (hAll n hn).1,by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hAll n hn).2 hβp.le⟩

end QuantitativeFollowup
