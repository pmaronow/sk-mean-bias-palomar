module
public import QuantitativeFollowup.NativeCenteredEnergyMomentBounds
public import QuantitativePaper.MainFluctuationTargets

@[expose] public section

/-! Exact mean-centered free-energy law, moments, and variance scaling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

def centeredFreeEnergyVariable (n : ℕ) (β : ℝ) (g : Couplings n) : ℝ :=
  logPartition n β g-(∫g,logPartition n β g ∂couplingLaw n)

def centeredFreeEnergyCGF (n : ℕ) (β s : ℝ) : ℝ :=
  cgf (centeredFreeEnergyVariable n β) (couplingLaw n) s

theorem centeredFreeEnergyVariable_eq_energy (n : ℕ) (β : ℝ) (hβ : β≠0) (g : Couplings n) :
    centeredFreeEnergyVariable n β g=β*(energyFreeEnergy n β g-
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)) := by
  have he : logPartition n β=(fun g=>β*energyFreeEnergy n β g):=by
    funext g
    unfold energyFreeEnergy
    exact (mul_div_cancel₀ _ hβ).symm
  unfold centeredFreeEnergyVariable
  rw [he,integral_const_mul]
  ring

theorem centeredFreeEnergyCGF_eq_energy (n : ℕ) (β s : ℝ) (hβ : β≠0) :
    centeredFreeEnergyCGF n β s=centeredEnergyCGF n β (β*s) := by
  unfold centeredFreeEnergyCGF centeredEnergyCGF cgf mgf
  congr 1
  apply integral_congr_ae
  exact .of_forall fun g=>by
    change Real.exp (s*centeredFreeEnergyVariable n β g)=
      Real.exp ((β*s)*(energyFreeEnergy n β g-(∫g,energyFreeEnergy n β g ∂couplingLaw n)))
    rw [centeredFreeEnergyVariable_eq_energy n β hβ]
    congr 1 <;> ring

theorem integrable_exp_centeredFreeEnergy (n : ℕ) (β s : ℝ) :
    Integrable (fun g=>Real.exp (s*centeredFreeEnergyVariable n β g)) (couplingLaw n) := by
  unfold centeredFreeEnergyVariable
  simp_rw [mul_sub,Real.exp_sub,div_eq_mul_inv]
  exact (integrable_exp_logPartition n β s).mul_const _

theorem centeredFreeEnergyCGF_nonneg (n : ℕ) (β s : ℝ) (hβ : β≠0) :
    0≤centeredFreeEnergyCGF n β s := by
  rw [centeredFreeEnergyCGF_eq_energy n β s hβ]
  exact centeredEnergyCGF_nonneg n β (β*s)

theorem native_centered_free_energy_cgf_negative_variance_bound (n : ℕ) (β : ℝ) (hβ : 0<β)
    (s : ℝ) (hs : s<0) :
    centeredFreeEnergyCGF n β s≤ s^2/2*freeEnergyVariance n β := by
  rw [centeredFreeEnergyCGF_eq_energy n β s hβ.ne',
    freeEnergyVariance_eq_scaled_energyVariance n β hβ.ne']
  have hh:=native_centered_energy_cgf_negative_variance_bound n β hβ (β*s)
    (mul_neg_of_pos_of_neg hβ hs)
  convert hh using 1 <;> ring

theorem centeredFreeEnergyCGF_eq_cgf_sub_mean (n : ℕ) (β s : ℝ) :
    centeredFreeEnergyCGF n β s=cgf (logPartition n β) (couplingLaw n) s-
      s*(∫g,logPartition n β g ∂couplingLaw n) := by
  have hh:=FourPapersCommon.cgf_add_constant (couplingLaw n) (logPartition n β) s
    (-(∫g,logPartition n β g ∂couplingLaw n)) (integrable_exp_logPartition n β s)
  convert hh using 1 <;> (try rfl) <;> ring

end QuantitativeFollowup
