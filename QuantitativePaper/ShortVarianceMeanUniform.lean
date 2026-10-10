module
public import QuantitativePaper.ShortVarianceMeanBalance
public import QuantitativePaper.SKGaussianVariance
public import QuantitativePaper.VectorInterpolationMonotonicity

@[expose] public section

/-! Application of the deterministic five-fourths optimization to the
actual SK model. Only the separately proved uniform scalar trial budget is
an input to this reusable reduction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem energyComparisonError_nonneg (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (lam : ℝ) (hlam : lam/β∈Ioo (0:ℝ) 1) :
    0≤energyComparisonError n β lam := by
  have hg := constrainedParisiValue_sub_completedFractionalPressure_nonneg n hn β
    (lam/β) hlam hβ.ne'
  rw [energyComparisonError,scalarEnergyValue,
    completedEnergyLaplace_eq_original n β lam hβ.ne',←sub_div]
  exact div_nonneg hg hβ.le

theorem energyMeanDeficit_variance_power_of_uniform_trial (β0 C L : ℝ)
    (hβ0 : 0<β0) (hC : 0≤C) (hL : 0<L) (hLβ : L≤β0/2)
    (hTrial : ∀ β : ℝ,β0≤β→∀ lam : ℝ,lam∈Ioc (0:ℝ) L→
      scalarEnergyValue β lam-scalarEnergyValue β 0≤C*lam^5) :
    ∃ c : ℝ,0<c ∧ ∀ n : ℕ,0<n→∀ β : ℝ,β0≤β→
      c*((variance (energyFreeEnergy n β) (couplingLaw n)+1/2)/(n:ℝ))^(5/4:ℝ)≤
        energyMeanDeficit n β := by
  obtain ⟨c,hc,hopt⟩ := short_variance_mean_optimization C L hC hL
  refine ⟨c,hc,?_⟩
  intro n hn β hβ0β
  have hβ : 0<β := hβ0.trans_le hβ0β
  have hv := energyCompletedVariance_density_le n hn β hβ
  apply hopt _ _ hv.1 (hv.2.trans (by norm_num))
  intro lam hlam hlamL
  have hlamβ : lam/β∈Ioo (0:ℝ) 1 := by
    refine ⟨div_pos hlam hβ,(div_lt_one hβ).2 ?_⟩
    linarith
  exact energyMeanDeficit_variance_balance n hn β hβ lam C hlam
    (hTrial β hβ0β lam ⟨hlam,hlamL⟩)
    (energyComparisonError_nonneg n hn β hβ lam hlamβ)

end QuantitativePaper
