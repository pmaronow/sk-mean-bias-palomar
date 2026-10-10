module
public import QuantitativePaper.CompletedEnergyLaplaceLimit
public import QuantitativePaper.ZeroTemperatureControlScalarLimit

@[expose] public section

/-! Actual finite/zero-temperature gap passage. Bounds on the finite
temperature gap pass to the genuine unbounded-profile variational value
and the actual completed finite-model ground-state Laplace transform. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 900000

theorem energyComparisonError_eq_fractional_gap (n : ℕ) (β lam : ℝ) (hβ : β ≠ 0) :
    energyComparisonError n β lam =
      (constrainedParisiValue β (lam/β) - completedFractionalPressure n β (lam/β)) / β := by
  rw [energyComparisonError, scalarEnergyValue, completedEnergyLaplace_eq_original n β lam hβ]
  ring

theorem energyComparisonError_third_rate_normalization (n : ℕ) (β lam : ℝ)
    (hβ : 0 < β) (hlam : 0 ≤ lam) :
    (β^(2/3 : ℝ) * (n : ℝ)^(-(2/3 : ℝ)) * (lam/β)^(-(1/3 : ℝ))) / β =
      (n : ℝ)^(-(2/3 : ℝ)) * lam^(-(1/3 : ℝ)) := by
  rw [Real.div_rpow hlam hβ.le]
  have he : β^(2/3 : ℝ) / β^(-(1/3 : ℝ)) = β := by
    rw [←Real.rpow_sub hβ]
    norm_num
  calc
    _ = (n : ℝ)^(-(2/3 : ℝ)) * lam^(-(1/3 : ℝ)) *
        ((β^(2/3 : ℝ) / β^(-(1/3 : ℝ))) / β) := by ring
    _ = _ := by rw [he, div_self hβ.ne', mul_one]

theorem tendsto_energyComparisonError_ground (n : ℕ) (hn : 0 < n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Tendsto (fun β : ℝ => energyComparisonError n β lam) atTop
      (𝓝 (zeroScalarValue lam - completedGroundLaplace n lam)) :=
  (scalar_zero_temperature_limit lam hlam).sub (tendsto_completedEnergyLaplace_ground n hn lam)

theorem ground_laplace_gap_of_energy_bounds (n : ℕ) (hn : 0 < n)
    (lam B : ℝ) (hlam : 0 ≤ lam)
    (hb : ∀ᶠ β : ℝ in atTop, 0 ≤ energyComparisonError n β lam ∧
      energyComparisonError n β lam ≤ B) :
    0 ≤ zeroScalarValue lam - completedGroundLaplace n lam ∧
      zeroScalarValue lam - completedGroundLaplace n lam ≤ B := by
  have hlim := tendsto_energyComparisonError_ground n hn lam hlam
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hb.mono fun _ h => h.1),
    le_of_tendsto_of_tendsto hlim tendsto_const_nhds (hb.mono fun _ h => h.2)⟩

theorem ground_mean_gap_of_energy_bounds (n : ℕ) (hn : 0 < n) (B : ℝ)
    (hb : ∀ᶠ β : ℝ in atTop, 0 ≤ energyComparisonError n β 0 ∧
      energyComparisonError n β 0 ≤ B) :
    0 ≤ groundScalarValue - groundMean n ∧ groundScalarValue - groundMean n ≤ B := by
  simpa only [groundScalarValue, completedGroundLaplace, ite_true] using
    ground_laplace_gap_of_energy_bounds n hn 0 B le_rfl hb

end QuantitativePaper
