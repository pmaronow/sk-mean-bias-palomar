module
public import QuantitativePaper.EnergyMomentIdentity
public import QuantitativePaper.SoftMaxLogMomentLimit
public import QuantitativePaper.NormalizedMomentStability
public import QuantitativePaper.Completion

@[expose] public section

/-! True finite-model zero-temperature passage at every real Laplace
parameter, including its expectation branch at zero. The independent
completion contributes the same exact linear correction on both sides. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1000000

theorem completedEnergyLaplace_eq_normalized (n : ℕ) (hn : 0 < n) (β lam : ℝ) :
    completedEnergyLaplace n β lam =
      normalizedEnergyMoment n β lam / (n : ℝ) + lam / (4 * (n : ℝ)) := by
  by_cases hl : lam = 0
  · subst lam
    rw [normalizedEnergyMoment_zero]
    simp only [completedEnergyLaplace, ite_true, zero_div, add_zero]
  · exact completedEnergyLaplace_eq n hn β hl

theorem completedGroundLaplace_eq_normalized (n : ℕ) (hn : 0 < n) (lam : ℝ) :
    completedGroundLaplace n lam =
      normalizedGroundMoment n lam / (n : ℝ) + lam / (4 * (n : ℝ)) := by
  by_cases hl : lam = 0
  · subst lam
    rw [normalizedGroundMoment_zero]
    simp only [completedGroundLaplace, ite_true, zero_div, add_zero, groundMean]
  · rw [completedGroundLaplace_eq n hn lam hl]
    unfold normalizedGroundMoment
    rw [normalizedCGF_of_ne _ _ hl]
    ring

theorem normalizedEnergyMoment_ground_distance (n : ℕ) (β lam : ℝ) (hβ : 0 < β) :
    |normalizedEnergyMoment n β lam - normalizedGroundMoment n lam| ≤
      (n : ℝ) * Real.log 2 / β := by
  apply normalizedCGF_sup_distance_bound (couplingLaw n)
    (energyFreeEnergy n β) (groundState n) ((n : ℝ) * Real.log 2 / β)
    (integrable_exp_energyFreeEnergy n β) (integrable_exp_groundState n)
  intro g
  rw [abs_of_nonneg (energyFreeEnergy_sub_groundState n β hβ g).1]
  exact (energyFreeEnergy_sub_groundState n β hβ g).2

theorem completedEnergyLaplace_ground_distance (n : ℕ) (hn : 0 < n)
    (β lam : ℝ) (hβ : 0 < β) :
    |completedEnergyLaplace n β lam - completedGroundLaplace n lam| ≤ Real.log 2 / β := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [completedEnergyLaplace_eq_normalized n hn, completedGroundLaplace_eq_normalized n hn]
  rw [add_sub_add_right_eq_sub, ←sub_div, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  convert normalizedEnergyMoment_ground_distance n β lam hβ using 1 <;> ring

theorem tendsto_completedEnergyLaplace_ground (n : ℕ) (hn : 0 < n) (lam : ℝ) :
    Tendsto (fun β : ℝ => completedEnergyLaplace n β lam) atTop
      (𝓝 (completedGroundLaplace n lam)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun β => norm_nonneg _)
    ((eventually_gt_atTop (0 : ℝ)).mono fun β hβ => by
      simpa only [Real.norm_eq_abs] using completedEnergyLaplace_ground_distance n hn β lam hβ)
  exact tendsto_const_nhds.div_atTop tendsto_id

end QuantitativePaper
