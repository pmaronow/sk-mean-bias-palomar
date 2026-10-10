module
public import QuantitativePaper.Model
public import FourPapersCommon.NormalizedCGF

@[expose] public section

/-! Actual finite-SK logarithmic moments, with the value and variance derivative
at zero. Gaussian normalized-moment convexity is a separate theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace QuantitativePaper

theorem integrable_exp_energyFreeEnergy (n : ℕ) (β lam : ℝ) :
    Integrable (fun g => Real.exp (lam*energyFreeEnergy n β g)) (couplingLaw n) := by
  convert integrable_exp_logPartition n β (lam/β) using 1
  funext g
  congr 1
  unfold energyFreeEnergy
  ring

theorem integrableExpSet_energyFreeEnergy (n : ℕ) (β : ℝ) :
    integrableExpSet (energyFreeEnergy n β) (couplingLaw n)=univ := by
  ext lam
  simp only [integrableExpSet,mem_setOf_eq,mem_univ,iff_true]
  exact integrable_exp_energyFreeEnergy n β lam

theorem memLp_two_energyFreeEnergy (n : ℕ) (β : ℝ) :
    MemLp (energyFreeEnergy n β) 2 (couplingLaw n) :=
by
  convert (memLp_two_logPartition n β).const_mul β⁻¹ using 1
  funext g
  unfold energyFreeEnergy
  ring

def normalizedEnergyMoment (n : ℕ) (β : ℝ) : ℝ → ℝ :=
  FourPapersCommon.normalizedCGF (couplingLaw n) (energyFreeEnergy n β)

theorem normalizedEnergyMoment_zero (n : ℕ) (β : ℝ) :
    normalizedEnergyMoment n β 0=∫g,energyFreeEnergy n β g ∂couplingLaw n := by
  apply FourPapersCommon.normalizedCGF_zero
  simp [integrableExpSet_energyFreeEnergy]

theorem normalizedEnergyMoment_of_ne (n : ℕ) (β : ℝ) {lam : ℝ} (hlam : lam≠0) :
    normalizedEnergyMoment n β lam=
      Real.log (∫g,Real.exp (lam*energyFreeEnergy n β g) ∂couplingLaw n)/lam :=
  FourPapersCommon.normalizedCGF_of_ne _ _ hlam

theorem hasDerivAt_normalizedEnergyMoment_zero (n : ℕ) (β : ℝ) :
    HasDerivAt (normalizedEnergyMoment n β)
      (variance (energyFreeEnergy n β) (couplingLaw n)/2) 0 := by
  apply FourPapersCommon.hasDerivAt_normalizedCGF_zero
  · simp [integrableExpSet_energyFreeEnergy]
  · exact memLp_two_energyFreeEnergy n β

theorem integrableExpSet_groundState (n : ℕ) :
    integrableExpSet (groundState n) (couplingLaw n)=univ := by
  ext lam
  simp only [integrableExpSet,mem_setOf_eq,mem_univ,iff_true]
  exact integrable_exp_groundState n lam

def normalizedGroundMoment (n : ℕ) : ℝ → ℝ :=
  FourPapersCommon.normalizedCGF (couplingLaw n) (groundState n)

theorem normalizedGroundMoment_zero (n : ℕ) :
    normalizedGroundMoment n 0=∫g,groundState n g ∂couplingLaw n := by
  apply FourPapersCommon.normalizedCGF_zero
  simp [integrableExpSet_groundState]

theorem hasDerivAt_normalizedGroundMoment_zero (n : ℕ) :
    HasDerivAt (normalizedGroundMoment n) (groundStateVariance n/2) 0 := by
  apply FourPapersCommon.hasDerivAt_normalizedCGF_zero
  · simp [integrableExpSet_groundState]
  · exact memLp_two_groundState n

end QuantitativePaper
