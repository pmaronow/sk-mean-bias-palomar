module
public import QuantitativePaper.VectorGauge
public import QuantitativePaper.NormalizedMoments
public import QuantitativeFollowup.ChenSK
public import Mathlib.Probability.Distributions.Exponential

@[expose] public section

/-! Actual exponential regularization of the finite SK free energy.
Its survival kernel is constructed directly from the physical Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1800000
variable {n : ℕ}

def regularizedEnergyTailKernel (n : ℕ) (β x : ℝ) (g : Couplings n) : ℝ :=
  Real.exp (-β*max (x-energyFreeEnergy n β g) 0)

def regularizedEnergyTail (n : ℕ) (β x : ℝ) : ℝ :=
  ∫g,regularizedEnergyTailKernel n β x g ∂couplingLaw n

theorem continuous_regularizedEnergyTailKernel (n : ℕ) (β x : ℝ) :
    Continuous (regularizedEnergyTailKernel n β x) := by
  unfold regularizedEnergyTailKernel energyFreeEnergy
  exact Real.continuous_exp.comp (((continuous_const.sub
    ((continuous_logPartition n β).div_const β)).max continuous_const).const_mul (-β))

theorem regularizedEnergyTailKernel_pos (n : ℕ) (β x : ℝ) (g : Couplings n) :
    0 < regularizedEnergyTailKernel n β x g := Real.exp_pos _

theorem regularizedEnergyTailKernel_le_one (n : ℕ) (β x : ℝ) (hβ : 0 ≤ β)
    (g : Couplings n) : regularizedEnergyTailKernel n β x g ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hm : 0 ≤ max (x-energyFreeEnergy n β g) 0 := le_max_right _ _
  nlinarith

theorem integrable_regularizedEnergyTailKernel (n : ℕ) (β x : ℝ) (hβ : 0 ≤ β) :
    Integrable (regularizedEnergyTailKernel n β x) (couplingLaw n) := by
  apply (integrable_const (1 : ℝ)).mono'
    (continuous_regularizedEnergyTailKernel n β x).aestronglyMeasurable
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_pos (regularizedEnergyTailKernel_pos n β x g)]
  exact regularizedEnergyTailKernel_le_one n β x hβ g

theorem regularizedEnergyTail_pos (n : ℕ) (β x : ℝ) (hβ : 0 ≤ β) :
    0 < regularizedEnergyTail n β x := by
  apply integral_pos_iff_support_of_nonneg_ae
    (.of_forall fun g=>(regularizedEnergyTailKernel_pos n β x g).le)
    (integrable_regularizedEnergyTailKernel n β x hβ) |>.2
  simp only [Function.support, ne_eq, ne_of_gt (regularizedEnergyTailKernel_pos n β x _),
    not_false_eq_true, Set.ofPred_true]
  simp

theorem regularizedEnergyTail_le_one (n : ℕ) (β x : ℝ) (hβ : 0 ≤ β) :
    regularizedEnergyTail n β x ≤ 1 := by
  have hi := integral_mono (integrable_regularizedEnergyTailKernel n β x hβ)
    (integrable_const (1 : ℝ)) (regularizedEnergyTailKernel_le_one n β x hβ)
  simpa only [regularizedEnergyTail, integral_const, probReal_univ, one_smul] using hi

theorem logPartition_couplingGauge (η : Configuration n) (β : ℝ) (g : Couplings n) :
    logPartition n β (couplingGauge η g) = logPartition n β g := by
  unfold logPartition Paper.skPartitionFunction
  simp_rw [energy_parameter, energy_gauge]
  congr 1
  exact (spinGaugeEquiv η).sum_comp (fun σ=>Real.exp (β*energy n g σ))

theorem energyFreeEnergy_couplingGauge (η : Configuration n) (β : ℝ) (g : Couplings n) :
    energyFreeEnergy n β (couplingGauge η g) = energyFreeEnergy n β g := by
  simp only [energyFreeEnergy, logPartition_couplingGauge]

theorem measurePreserving_couplingGauge (η : Configuration n) :
    MeasurePreserving (couplingGauge η) (couplingLaw n) (couplingLaw n) := by
  have hpres (e : Edge n) : MeasurePreserving
      (fun z : ℝ=>(Paper.spinSign (η e.val.1)*Paper.spinSign (η e.val.2))*z)
      (gaussianReal 0 1) (gaussianReal 0 1) := by
    refine ⟨by fun_prop,?_⟩
    rw [gaussianReal_map_const_mul]
    cases h₁ : η e.val.1 <;> cases h₂ : η e.val.2 <;>
      simp [Paper.spinSign, h₁, h₂]
  exact measurePreserving_pi _ _ hpres

theorem regularizedEnergyTailKernel_eq_spin_sum (n : ℕ) (β x : ℝ) (hβ : 0 < β)
    (g : Couplings n) :
    regularizedEnergyTailKernel n β x g =
      ∑σ : Configuration n,Real.exp (β*energy n g σ-β*max (energyFreeEnergy n β g) x) := by
  have hp : ∑σ : Configuration n,Real.exp (β*energy n g σ) =
      Real.exp (β*energyFreeEnergy n β g) := by
    rw [energyFreeEnergy, mul_div_cancel₀ _ hβ.ne']
    rw [logPartition, Real.exp_log (Paper.skPartitionFunction_pos β 0 g)]
    unfold Paper.skPartitionFunction
    simp_rw [energy_parameter]
  have he : β*energyFreeEnergy n β g-β*max (energyFreeEnergy n β g) x =
      -β*max (x-energyFreeEnergy n β g) 0 := by
    rcases le_total x (energyFreeEnergy n β g) with h|h
    · rw [max_eq_left h, max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      ring
  simp_rw [Real.exp_sub]
  rw [← Finset.sum_div, hp, ← Real.exp_sub, he]
  rfl

def regularizedEnergySpinTerm (n : ℕ) (β x : ℝ) (σ : Configuration n)
    (g : Couplings n) : ℝ :=
  Real.exp (β*energy n g σ-β*max (energyFreeEnergy n β g) x)

def allPositiveConfiguration (n : ℕ) : Configuration n := fun _=>true

theorem spinGauge_allPositive (η : Configuration n) :
    spinGauge η (allPositiveConfiguration n) = η := by
  funext i
  cases h : η i <;> simp [spinGauge,allPositiveConfiguration,h]

theorem continuous_regularizedEnergySpinTerm (n : ℕ) (β x : ℝ) (σ : Configuration n) :
    Continuous (regularizedEnergySpinTerm n β x σ) := by
  unfold regularizedEnergySpinTerm energyFreeEnergy
  have hE : Continuous (fun g : Couplings n=>energy n g σ) :=
    Paper.continuous_skHamiltonian 1 0 σ
  exact Real.continuous_exp.comp ((hE.const_mul β).sub
    ((((continuous_logPartition n β).div_const β).max continuous_const).const_mul β))

theorem regularizedEnergySpinTerm_le_one (n : ℕ) (β x : ℝ) (hβ : 0 < β)
    (σ : Configuration n) (g : Couplings n) : regularizedEnergySpinTerm n β x σ g ≤ 1 := by
  have hs : regularizedEnergySpinTerm n β x σ g ≤ regularizedEnergyTailKernel n β x g := by
    rw [regularizedEnergyTailKernel_eq_spin_sum n β x hβ g]
    change Real.exp _ ≤ _
    exact Finset.single_le_sum
      (f:=fun τ : Configuration n=>Real.exp (β*energy n g τ-β*max (energyFreeEnergy n β g) x))
      (fun τ _=>(Real.exp_pos _).le) (Finset.mem_univ σ)
  exact hs.trans (regularizedEnergyTailKernel_le_one n β x hβ.le g)

theorem integrable_regularizedEnergySpinTerm (n : ℕ) (β x : ℝ) (hβ : 0 < β)
    (σ : Configuration n) : Integrable (regularizedEnergySpinTerm n β x σ) (couplingLaw n) := by
  apply (integrable_const (1 : ℝ)).mono'
    (continuous_regularizedEnergySpinTerm n β x σ).aestronglyMeasurable
  filter_upwards with g
  rw [Real.norm_eq_abs,abs_of_pos (show 0 < regularizedEnergySpinTerm n β x σ g from
    Real.exp_pos _)]
  exact regularizedEnergySpinTerm_le_one n β x hβ σ g

theorem integral_regularizedEnergySpinTerm_gauge (n : ℕ) (β x : ℝ)
    (σ : Configuration n) :
    (∫g,regularizedEnergySpinTerm n β x σ g ∂couplingLaw n) =
      ∫g,regularizedEnergySpinTerm n β x (allPositiveConfiguration n) g ∂couplingLaw n := by
  have hp := measurePreserving_couplingGauge σ
  have hG : HasLaw (couplingGauge σ) (couplingLaw n) (couplingLaw n) :=
    ⟨hp.measurable.aemeasurable,hp.map_eq⟩
  have he : (fun g=>regularizedEnergySpinTerm n β x (allPositiveConfiguration n)
      (couplingGauge σ g)) = regularizedEnergySpinTerm n β x σ := by
    funext g
    simp only [regularizedEnergySpinTerm,energy_gauge,spinGauge_allPositive,
      energyFreeEnergy_couplingGauge]
  rw [←he]
  exact hG.integral_comp
    (continuous_regularizedEnergySpinTerm n β x (allPositiveConfiguration n)).aestronglyMeasurable

/-- Exact finite-spin gauge identity for the regularized survival function. -/
theorem regularizedEnergyTail_gauge_formula (n : ℕ) (β x : ℝ) (hβ : 0 < β) :
    regularizedEnergyTail n β x = (2 : ℝ)^n*
      (∫g,regularizedEnergySpinTerm n β x (allPositiveConfiguration n) g ∂couplingLaw n) := by
  unfold regularizedEnergyTail
  simp_rw [regularizedEnergyTailKernel_eq_spin_sum n β x hβ]
  change (∫g,∑σ : Configuration n,regularizedEnergySpinTerm n β x σ g ∂couplingLaw n) = _
  rw [integral_finsetSum _ (fun σ _=>integrable_regularizedEnergySpinTerm n β x hβ σ)]
  simp_rw [integral_regularizedEnergySpinTerm_gauge n β x]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,configuration_card,Nat.cast_pow,
    Nat.cast_ofNat]

end QuantitativePaper
