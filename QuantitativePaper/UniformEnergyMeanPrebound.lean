module
public import QuantitativePaper.ShortVarianceMeanUniform

@[expose] public section

/-! The actual midpoint Chen inequality cancels the diagonal correction
and reduces the mean deficit to a scalar trial and one comparison error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem scalarEnergyValue_gap_nonneg (β lam : ℝ) (hβ : 0<β)
    (hlam : lam/β∈Icc (0:ℝ) 1) : 0≤ scalarEnergyValue β lam-scalarEnergyValue β 0 := by
  unfold scalarEnergyValue
  rw [zero_div]
  exact sub_nonneg.mpr (div_le_div_of_nonneg_right
    (constrainedParisiValue_mono β hlam.1 hlam.2) hβ.le)

theorem energyMeanDeficit_midpoint_bound (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (lam C : ℝ) (hlam : 0<lam) (hlamβ : (2*lam)/β∈Ioo (0:ℝ) 1)
    (htrial : scalarEnergyValue β (2*lam)-scalarEnergyValue β 0≤C*(2*lam)^5) :
    energyMeanDeficit n β≤32*C*lam^5+2*energyComparisonError n β lam := by
  have hc := (convexOn_scalarCenteredEnergyMoment n β hβ).2 (mem_univ 0) (mem_univ (2*lam))
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul,mul_zero,zero_add] at hc
  rw [show (1/2:ℝ)*(2*lam)=lam by ring,scalarCenteredEnergyMoment_zero] at hc
  have herror2 := energyComparisonError_nonneg n hn β hβ (2*lam) hlamβ
  have hlam1 : lam/β∈Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hβ).2
      have ht := (div_lt_one hβ).1 hlamβ.2
      linarith
  have hgap := scalarEnergyValue_gap_nonneg β lam hβ hlam1
  rw [energy_tail_moment_exact n hn β hlam.ne',
    energy_tail_moment_exact n hn β (show 2*lam≠0 by positivity)] at hc
  have hd : (2*lam)/(4*(n:ℝ))=2*(lam/(4*(n:ℝ))) := by ring
  rw [hd] at hc
  nlinarith [show C*(2*lam)^5=32*C*lam^5 by ring]

end QuantitativePaper
