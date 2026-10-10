module
public import QuantitativePaper.RegularizedEnergyLogConcavity
public import QuantitativePaper.VectorSharpMassBounds

@[expose] public section

/-! The sharp physical finite-SK Euclidean disorder Lipschitz constant.
The coefficient norm is computed from the actual unordered-pair Hamiltonian. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace QuantitativePaper
open QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1000000

def skGaussianEnergyCoefficient (n : ℕ) (σ : Configuration n) : SKGaussianSpace n:=
  WithLp.toLp 2 (fun e=>1/Real.sqrt (n:ℝ)*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2))

theorem gaussianEnergyLinear_eq_inner (n : ℕ) (σ : Configuration n) (z : SKGaussianSpace n) :
    gaussianEnergyLinear n σ z=⟪skGaussianEnergyCoefficient n σ,z⟫:=by
  rw [gaussianEnergyLinear_apply]
  unfold energy Paper.skHamiltonian
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [skGaussianEnergyCoefficient,star_trivial,dotProduct,
    zero_mul,add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  change (1/Real.sqrt (n:ℝ))*(z e*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2))=_
  ring

theorem skGaussianEnergyCoefficient_norm_sq (n : ℕ) (hn : 0<n) (σ : Configuration n) :
    ‖skGaussianEnergyCoefficient n σ‖^2=((n:ℝ)-1)/2:=by
  have hh:=Paper.unordered_pair_sum_square (fun _ : Fin n=>(1:ℝ)) (fun _=>by norm_num)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,one_mul] at hh
  have hedge : (Fintype.card (Edge n):ℝ)/ (n:ℝ)=((n:ℝ)-1)/2:=by
    have hnr : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
    apply (div_eq_iff hnr).mpr
    nlinarith
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑e : Edge n,(1/Real.sqrt (n:ℝ)*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2))^2)=_
  simp only [mul_pow,Paper.spinSign_sq,mul_one,one_div_pow,Real.sq_sqrt (Nat.cast_nonneg n),
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  convert hedge using 1 <;> ring

theorem norm_skGaussianEnergyCoefficient (n : ℕ) (hn : 0<n) (σ : Configuration n) :
    ‖skGaussianEnergyCoefficient n σ‖=Real.sqrt (((n:ℝ)-1)/2):=by
  rw [←skGaussianEnergyCoefficient_norm_sq n hn σ,Real.sqrt_sq (norm_nonneg _)]

theorem lipschitz_energyFreeEnergy_gaussian (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) :
    LipschitzWith (Real.sqrt (((n:ℝ)-1)/2)).toNNReal
      (fun z : SKGaussianSpace n=>energyFreeEnergy n β (skGaussianDisorderLinear n z)):=by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq,dist_eq_norm,Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  unfold energyFreeEnergy
  rw [←sub_div,abs_div,abs_of_pos hβ]
  apply (div_le_iff₀ hβ).mpr
  have he (y : SKGaussianSpace n) : logPartition n β (skGaussianDisorderLinear n y)=
      terminalPotential (fun σ=>β*energy n (skGaussianDisorderLinear n y) σ):=by
    unfold logPartition terminalPotential terminalPartition Paper.skPartitionFunction
    simp_rw [energy_parameter]
  rw [he z,he w]
  apply abs_terminalPotential_sub_le
  intro σ
  rw [←gaussianEnergyLinear_apply,←gaussianEnergyLinear_apply,←mul_sub,←map_sub,
    gaussianEnergyLinear_eq_inner,abs_mul,abs_of_pos hβ]
  have hb:=abs_real_inner_le_norm (skGaussianEnergyCoefficient n σ) (z-w)
  rw [norm_skGaussianEnergyCoefficient n hn σ] at hb
  nlinarith

end QuantitativePaper
