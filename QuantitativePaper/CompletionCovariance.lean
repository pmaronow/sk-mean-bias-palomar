module
public import QuantitativePaper.GOEQuadratic

@[expose] public section

/-! Actual exact SK overlap covariance under the concrete product Gaussian
completion, with its literal half-quadratic GOE representation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
namespace QuantitativePaper

def overlap (n : ℕ) (σ τ : Configuration n) : ℝ :=
  (1/(n : ℝ))*∑ i,Paper.spinSign (σ i)*Paper.spinSign (τ i)
def completedEnergy (n : ℕ) (p : Couplings n × ℝ) (σ : Configuration n) : ℝ := energy n p.1 σ+p.2

theorem couplingCoordinate_law {n : ℕ} (e : Edge n) :
    (couplingLaw n).map (fun g => g e) = gaussianReal 0 1 :=
  (measurePreserving_eval (fun _ : Edge n => gaussianReal 0 1) e).map_eq

theorem couplingCoordinates_independent (n : ℕ) :
    iIndepFun (fun e : Edge n => fun g : Couplings n => g e) (couplingLaw n) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem memLp_two_energy (n : ℕ) (σ : Configuration n) : MemLp (fun g => energy n g σ) 2 (couplingLaw n) := by
  unfold energy Paper.skHamiltonian
  simp only [zero_mul,add_zero]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro e _
  have he := Paper.standardGaussianCoordinate_gaussian (couplingLaw n) (fun g => g e)
    (measurable_pi_apply e) (couplingCoordinate_law e)
  exact (he.memLp_two.mul_const _).mul_const _

theorem integral_energy (n : ℕ) (σ : Configuration n) : (∫ g,energy n g σ ∂couplingLaw n) = 0 := by
  unfold energy Paper.skHamiltonian
  simp only [zero_mul,add_zero]
  rw [integral_const_mul,integral_finsetSum _ (fun e _ =>
    ((Paper.integrable_skCoupling_coordinate e).mul_const _).mul_const _)]
  have he (e : Edge n) : (∫ g,g e ∂couplingLaw n) = 0 :=
    Paper.standardGaussianCoordinate_mean _ _ (measurable_pi_apply e) (couplingCoordinate_law e)
  simp_rw [integral_mul_const,he,zero_mul]
  simp

def energyCoefficient {n : ℕ} (σ : Configuration n) (e : Edge n) : ℝ :=
  (1/Real.sqrt (n : ℝ))*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)

private theorem energy_eq_linear (n : ℕ) (σ : Configuration n) (g : Couplings n) :
    energy n g σ = ∑ e : Edge n,energyCoefficient σ e*g e := by
  unfold energy Paper.skHamiltonian energyCoefficient
  simp only [zero_mul,add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem integral_energy_mul (n : ℕ) (σ τ : Configuration n) :
    (∫ g,energy n g σ*energy n g τ ∂couplingLaw n) =
      ∑ e : Edge n,energyCoefficient σ e*energyCoefficient τ e := by
  simp_rw [energy_eq_linear]
  exact Paper.independent_standardGaussian_linear_covariance
    (fun e : Edge n => fun g : Couplings n => g e) (fun e => measurable_pi_apply e)
    (fun e => couplingCoordinate_law e) (couplingCoordinates_independent n) _ _

theorem memLp_two_completedEnergy (n : ℕ) (σ : Configuration n) :
    MemLp (fun p => completedEnergy n p σ) 2 (completionLaw n) := by
  have hD : MemLp (fun d : ℝ => d) 2 (gaussianReal 0 (1/2)) :=
    MemLp.ae_eq (Eventually.of_forall fun d => rfl)
      (memLp_id_gaussianReal' (p := 2) (by norm_num))
  exact ((memLp_two_energy n σ).comp_fst _).add (hD.comp_snd _)

theorem integral_completedEnergy (n : ℕ) (σ : Configuration n) :
    (∫ p,completedEnergy n p σ ∂completionLaw n) = 0 := by
  have hD : Integrable (fun d : ℝ => d) (gaussianReal 0 (1/2)) := by
    exact ((memLp_id_gaussianReal (μ := 0) (v := 1/2) 1).integrable le_rfl).congr
      (Eventually.of_forall fun d => rfl)
  have hE : Integrable (fun p : Couplings n × ℝ => energy n p.1 σ) (completionLaw n) :=
    (Paper.integrable_skHamiltonian 1 0 σ).comp_fst _
  have hNoise : Integrable (fun p : Couplings n × ℝ => p.2) (completionLaw n) := hD.comp_snd _
  have hadd := integral_add hE hNoise
  unfold completedEnergy
  rw [hadd]
  unfold completionLaw
  rw [
    integral_fun_fst (fun g => energy n g σ),integral_fun_snd (fun d : ℝ => d),
    integral_energy,integral_id_gaussianReal]
  simp

theorem integral_completedEnergy_mul (n : ℕ) (σ τ : Configuration n) :
    (∫ p,completedEnergy n p σ*completedEnergy n p τ ∂completionLaw n) =
      (∑ e : Edge n,energyCoefficient σ e*energyCoefficient τ e)+(1/2 : ℝ) := by
  have hσ := (memLp_two_energy n σ).comp_fst (gaussianReal 0 (1/2))
  have hτ := (memLp_two_energy n τ).comp_fst (gaussianReal 0 (1/2))
  have hD0 : MemLp (fun d : ℝ => d) 2 (gaussianReal 0 (1/2)) :=
    MemLp.ae_eq (Eventually.of_forall fun d => rfl)
      (memLp_id_gaussianReal' (p := 2) (by norm_num))
  have hD := hD0.comp_snd (couplingLaw n)
  have heq : (fun p => completedEnergy n p σ*completedEnergy n p τ) =
      fun p : Couplings n × ℝ => (energy n p.1 σ*energy n p.1 τ+energy n p.1 σ*p.2)+
        (energy n p.1 τ*p.2+p.2*p.2) := by
    funext p
    unfold completedEnergy
    ring
  have hv : (∫ d : ℝ,d*d ∂gaussianReal 0 (1/2)) = (1/2 : ℝ) := by
    have hh := variance_fun_id_gaussianReal (μ := 0) (v := 1/2)
    rw [variance_eq_integral (show AEMeasurable (fun d : ℝ => d) (gaussianReal 0 (1/2)) from measurable_id.aemeasurable),integral_id_gaussianReal] at hh
    simpa [pow_two] using hh
  have hEE : Integrable (fun p : Couplings n × ℝ => energy n p.1 σ*energy n p.1 τ) (completionLaw n) := hσ.integrable_mul hτ
  have hEDσ : Integrable (fun p : Couplings n × ℝ => energy n p.1 σ*p.2) (completionLaw n) := hσ.integrable_mul hD
  have hEDτ : Integrable (fun p : Couplings n × ℝ => energy n p.1 τ*p.2) (completionLaw n) := hτ.integrable_mul hD
  have hDD : Integrable (fun p : Couplings n × ℝ => p.2*p.2) (completionLaw n) := hD.integrable_mul hD
  have hadd := integral_add (hEE.add hEDσ) (hEDτ.add hDD)
  have hleft := integral_add hEE hEDσ
  have hright := integral_add hEDτ hDD
  simp only [Pi.add_apply] at hadd hleft hright
  rw [heq,hadd,hleft,hright]
  unfold completionLaw
  rw [integral_fun_fst (fun g => energy n g σ*energy n g τ),
    integral_prod_mul (fun g => energy n g σ) (fun d : ℝ => d),
    integral_prod_mul (fun g => energy n g τ) (fun d : ℝ => d),
    integral_fun_snd (fun d : ℝ => d*d),integral_energy_mul,integral_id_gaussianReal,hv]
  simp

theorem completedEnergy_covariance (n : ℕ) (hn : 0 < n) (σ τ : Configuration n) :
    covariance (fun p => completedEnergy n p σ) (fun p => completedEnergy n p τ) (completionLaw n) =
      (n : ℝ)/2*overlap n σ τ^2 := by
  rw [covariance_eq_sub (memLp_two_completedEnergy n σ) (memLp_two_completedEnergy n τ),
    integral_completedEnergy,integral_completedEnergy,mul_zero,sub_zero]
  simp only [Pi.mul_apply]
  rw [integral_completedEnergy_mul]
  have hn0 := hn.ne'
  have hcoef := Paper.physicalSKCoefficient_covariance n 1 σ τ
  rw [Fintype.sum_option] at hcoef
  have hcommon : Paper.physicalSKCoefficient n 1 σ none*Paper.physicalSKCoefficient n 1 τ none = (1/2 : ℝ) := by
    simp only [Paper.physicalSKCoefficient,Paper.skCommonNoiseCoefficient,hn0,ite_false,←pow_two,div_pow]
    rw [Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]
    norm_num
  have hedge (e : Edge n) : Paper.physicalSKCoefficient n 1 σ (some e)*
      Paper.physicalSKCoefficient n 1 τ (some e) = energyCoefficient σ e*energyCoefficient τ e := by
    simp only [Paper.physicalSKCoefficient,energyCoefficient]
    ring
  simp_rw [hcommon,hedge] at hcoef
  unfold overlap
  nlinarith [hcoef]

end QuantitativePaper
