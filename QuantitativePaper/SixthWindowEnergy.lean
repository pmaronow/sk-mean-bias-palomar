module
public import QuantitativePaper.ShortVarianceMeanUniform
public import QuantitativePaper.EnergyMomentProposition
public import QuantitativePaper.SixthWindowConsequences

@[expose] public section

/-! Actual SK cumulant identities produce the upper and lower sixth-power
window from the scalar floor costs and the improved comparison estimate.
The actual ground-state passage retains the same constants. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem scalarCenteredEnergyLogMoment_eq_mul (n : ℕ) (hn : 0<n) (β lam : ℝ)
    (hlam : lam≠0) :
    scalarCenteredEnergyLogMoment n β lam=(n:ℝ)*lam*scalarCenteredEnergyMoment n β lam := by
  rw [scalarCenteredEnergyMoment_of_ne n hn β hlam]
  exact (mul_div_cancel₀ _ (mul_ne_zero (by exact_mod_cast hn.ne') hlam)).symm

theorem energy_sixth_moment_upper (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (lam C : ℝ) (hlam : 0<lam) (hlamβ : lam/β∈Ioo (0:ℝ) 1)
    (htrial : scalarEnergyValue β lam-scalarEnergyValue β 0≤C*lam^5) :
    scalarCenteredEnergyLogMoment n β lam≤C*(n:ℝ)*lam^6 := by
  have he:=energyComparisonError_nonneg n hn β hβ lam hlamβ
  have hh : scalarCenteredEnergyMoment n β lam≤C*lam^5 := by
    rw [energy_tail_moment_exact n hn β hlam.ne']
    have hnR : 0<(n:ℝ) := by exact_mod_cast hn
    have hdiag : 0≤lam/(4*(n:ℝ)) := by positivity
    linarith
  rw [scalarCenteredEnergyLogMoment_eq_mul n hn β lam hlam.ne']
  convert mul_le_mul_of_nonneg_left hh (by positivity : 0≤(n:ℝ)*lam) using 1 <;> ring

theorem energy_sixth_moment_lower (n : ℕ) (hn : 0<n) (β lam c0 : ℝ)
    (hlam : 0<lam)
    (hcost : c0*lam^5≤ scalarEnergyValue β lam-scalarEnergyValue β 0)
    (herror : energyComparisonError n β lam≤c0/4*lam^5)
    (hdiag : lam^2/4≤c0/4*(n:ℝ)*lam^6) :
    c0/2*(n:ℝ)*lam^6≤ scalarCenteredEnergyLogMoment n β lam := by
  rw [scalarCenteredEnergyLogMoment_eq_mul n hn β lam hlam.ne',
    energy_tail_moment_exact n hn β hlam.ne']
  have hpre:=mul_le_mul_of_nonneg_left (show c0*lam^5-c0/4*lam^5≤
      scalarEnergyValue β lam-scalarEnergyValue β 0-energyComparisonError n β lam by linarith)
    (by positivity : 0≤(n:ℝ)*lam)
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : (n:ℝ)*lam*(lam/(4*(n:ℝ)))=lam^2/4 := by field_simp <;> ring
  rw [mul_sub,he]
  nlinarith

theorem ground_sixth_moment_bounds_of_energy (n : ℕ) (lam A B β0 : ℝ)
    (henergy : ∀β : ℝ,β0≤β→A≤ scalarCenteredEnergyLogMoment n β lam ∧
      scalarCenteredEnergyLogMoment n β lam≤B) :
    A≤ scalarCenteredGroundLogMoment n lam ∧ scalarCenteredGroundLogMoment n lam≤B := by
  have hlim:=scalarCenteredEnergyLogMoment_ground_limit n lam
  have hev : ∀ᶠβ : ℝ in atTop,A≤ scalarCenteredEnergyLogMoment n β lam ∧
      scalarCenteredEnergyLogMoment n β lam≤B := by
    filter_upwards [eventually_ge_atTop β0] with β hβ
    exact henergy β hβ
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hev.mono fun _ h=>h.1),
    le_of_tendsto_of_tendsto hlim tendsto_const_nhds (hev.mono fun _ h=>h.2)⟩

end QuantitativePaper
