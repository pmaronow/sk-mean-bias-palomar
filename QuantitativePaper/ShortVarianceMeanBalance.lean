module
public import QuantitativePaper.EnergyMomentIdentity
public import QuantitativePaper.ShortVarianceMeanCalculus

@[expose] public section

/-! The actual Chen tangent inequality and independent diagonal completion
produce the paper's exact variance/mean balance. The scalar trial estimate
is kept as a deterministic reusable input until its uniform theorem is applied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem energyMeanDeficit_variance_balance (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (lam C : ℝ) (hlam : 0<lam)
    (hTrial : scalarEnergyValue β lam-scalarEnergyValue β 0≤C*lam^5)
    (hError : 0≤energyComparisonError n β lam) :
    ((variance (energyFreeEnergy n β) (couplingLaw n)+1/2)/(n:ℝ))*lam/2-C*lam^5≤
      energyMeanDeficit n β:=by
  let f:=scalarCenteredEnergyMoment n β
  have hd:=hasDerivAt_scalarCenteredEnergyMoment_zero n β
  have hs:=(convexOn_scalarCenteredEnergyMoment n β hβ).deriv_le_slope
    (mem_univ 0) (mem_univ lam) hlam hd.differentiableAt
  have htan:=mul_le_mul_of_nonneg_right hs hlam.le
  rw [hd.deriv] at htan
  simp only [slope,sub_zero,smul_eq_mul,vsub_eq_sub] at htan
  rw [scalarCenteredEnergyMoment_zero] at htan
  have he : (lam⁻¹*(f lam-(-energyMeanDeficit n β)))*lam=
      f lam+energyMeanDeficit n β:=by field_simp;ring
  change variance (energyFreeEnergy n β) (couplingLaw n)/(2*(n:ℝ))*lam≤_ at htan
  rw [he] at htan
  have hf:=energy_tail_moment_exact n hn β hlam.ne'
  have hupper : f lam≤C*lam^5-lam/(4*(n:ℝ)):=by dsimp only [f];rw [hf];linarith
  have hnr : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  have ha : ((variance (energyFreeEnergy n β) (couplingLaw n)+1/2)/(n:ℝ))*lam/2=
      variance (energyFreeEnergy n β) (couplingLaw n)/(2*(n:ℝ))*lam+lam/(4*(n:ℝ)):=by
    field_simp
    ring
  rw [ha]
  linarith

end QuantitativePaper
