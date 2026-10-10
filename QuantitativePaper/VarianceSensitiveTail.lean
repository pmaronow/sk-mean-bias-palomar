module
public import QuantitativePaper.RegularizedEnergyLaw
public import FourPapersCommon.LogConcaveSurvivalTail

@[expose] public section

/-! Literal quantitative Lemma 5.9: the true finite-SK upper tail on its
actual standard-deviation scale, including the independent exponential
regularization and the exact printed constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1500000

 def varianceTailScale (n : ℕ) (β : ℝ) : ℝ :=
  Real.sqrt (variance (energyFreeEnergy n β) (couplingLaw n)+β⁻¹^2)
 def varianceTailRate : ℝ := Real.log 3/8

 theorem varianceTailScale_pos (n : ℕ) (β : ℝ) (hβ : 0<β) :
    0<varianceTailScale n β := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_nonneg_of_pos (variance_nonneg _ _) (sq_pos_of_pos (inv_pos.mpr hβ))

 theorem inverse_temperature_le_varianceTailScale (n : ℕ) (β : ℝ) :
    β⁻¹≤varianceTailScale n β :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (variance_nonneg _ _))

 theorem varianceTailScale_sq (n : ℕ) (β : ℝ) :
    (varianceTailScale n β)^2=variance (energyFreeEnergy n β) (couplingLaw n)+β⁻¹^2 :=
  Real.sq_sqrt (add_nonneg (variance_nonneg _ _) (sq_nonneg _))

 theorem regularizedEnergyTail_variance_bound (n : ℕ) (β : ℝ) (hβ : 0<β)
    (y : ℝ) (hy : 0≤y) :
    regularizedEnergyTail n β ((∫g,energyFreeEnergy n β g ∂couplingLaw n)+y)≤
      3*Real.exp (-Real.log 3*y/(4*varianceTailScale n β)) := by
  let P:=regularizedEnergyLaw n β
  let T:=regularizedEnergyVariable n β
  let _:=regularizedEnergyLaw_probability n β hβ
  have hS : realSurvival P T=regularizedEnergyTail n β := by
    funext x
    exact (regularizedEnergyTail_eq_survival n β x hβ).symm
  have hh:=logConcave_survival_tail (P:=P) (T:=T)
    (continuous_regularizedEnergyVariable n β).measurable (memLp_regularizedEnergyVariable n β hβ)
    (fun x=>by rw [hS];exact regularizedEnergyTail_pos n β x hβ.le)
    (by rw [hS];exact concaveOn_log_regularizedEnergyTail n β hβ)
    (varianceTailScale n β) β⁻¹ (varianceTailScale_pos n β hβ)
    (by rw [variance_regularizedEnergyVariable n β hβ,varianceTailScale_sq])
    (inverse_temperature_le_varianceTailScale n β) y hy
  rw [hS,integral_regularizedEnergyVariable n β hβ] at hh
  convert hh using 1
  congr 1
  ring

 theorem variance_sensitive_energy_tail (n : ℕ) (_hn : 0<n) (β : ℝ) (hβ : 0<β)
    (y : ℝ) (hy : 0≤y) :
    (couplingLaw n).real {g | y≤energyFreeEnergy n β g-
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)}≤
      3*Real.exp (-2*varianceTailRate*y/varianceTailScale n β) := by
  have hset : {g : Couplings n | y≤energyFreeEnergy n β g-
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)}=
      {g | (∫g,energyFreeEnergy n β g ∂couplingLaw n)+y≤energyFreeEnergy n β g} := by
    ext g
    simp only [mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  convert (energyUpperTail_le_regularizedEnergyTail n β _ hβ).trans
    (regularizedEnergyTail_variance_bound n β hβ y hy) using 1
  congr 2
  unfold varianceTailRate
  ring

 def VarianceSensitiveTailTarget : Prop :=
  ∀n : ℕ,0<n→∀β : ℝ,0<β→∀y : ℝ,0≤y→
    (couplingLaw n).real {g | y≤energyFreeEnergy n β g-
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)}≤
      3*Real.exp (-2*varianceTailRate*y/varianceTailScale n β)

 theorem variance_sensitive_tail : VarianceSensitiveTailTarget :=
  variance_sensitive_energy_tail

end QuantitativePaper
