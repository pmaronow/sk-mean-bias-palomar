module
public import QuantitativePaper.VectorProfileKernelEnvelopes
public import QuantitativePaper.ScalarGaussianBoundedIntervalDomination
public import QuantitativePaper.VectorProfileEndpointSmooth
public import QuantitativePaper.VectorExponentialLocalization

@[expose] public section

/-! Actual dominated disorder/profile differentiation inputs for arbitrary
real fractional outer tilts, including zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem exists_vectorProfileJointFunction_common_exp_jets_all_theta (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (N j : ℕ) (a b : ℝ) :
    ∃ C R : ℝ,1≤C ∧ 0≤R ∧ ∀ r,r≤N→∀ y : ℝ×VectorParameter n,y.1∈Ioo a b→
      ‖iteratedFDeriv ℝ r (vectorProfileJointFunction s₀ s₁ β t j) y‖≤C*Real.exp (R*‖y‖) := by
  obtain ⟨hs,K,D,hK,hD,hj⟩:=vectorProfileJointFunction_smooth_exp_jets_all_theta
    (n:=n) s₀ s₁ β t N j a b
  obtain ⟨B,L,hB,hL,hvalue⟩:=vectorProfileJointFunction_linear_growth_all_theta
    (n:=n) s₀ s₁ β t j a b
  exact exists_common_exponential_jet_envelope N _ {y : ℝ×VectorParameter n|y.1∈Ioo a b}
    B L K D hB hL hK (zero_le_one.trans hD)
    (fun y hy=>hvalue y ⟨hy.1.le,hy.2.le⟩) hj

theorem exists_vectorProfileJointExponential_exp_jets_all_theta (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (outer : ℝ) (N j : ℕ) (a b : ℝ) :
    ∃C R : ℝ,0≤C ∧ 0≤R ∧ ∀r,r≤N→∀z : ℝ×VectorParameter n,z.1∈Ioo a b→
      ‖iteratedFDeriv ℝ r (fun y=>Real.exp (outer*vectorProfileJointFunction s₀ s₁ β t j y)) z‖≤
        C*Real.exp (R*‖z‖) := by
  let U : Set (ℝ×VectorParameter n):={z|z.1∈Ioo a b}
  have hU : IsOpen U:=isOpen_Ioo.preimage continuous_fst
  obtain ⟨hs,K,D,hK,hD,hj⟩:=vectorProfileJointFunction_smooth_exp_jets_all_theta
    (n:=n) s₀ s₁ β t N j a b
  obtain ⟨B,L,hB,hL,hv⟩:=vectorProfileJointFunction_linear_growth_all_theta (n:=n) s₀ s₁ β t j a b
  let M:=max 1 |outer|
  have hM : 1≤M:=le_max_left _ _
  let g:=fun y : ℝ×VectorParameter n=>outer*vectorProfileJointFunction s₀ s₁ β t j y
  have hg : ContDiffOn ℝ N g U:=contDiffOn_const.mul hs
  have hgj : ∀ r, 1 ≤ r → r ≤ N → ∀ z∈U,
      ‖iteratedFDeriv ℝ r g z‖≤((M*K)*Real.exp (D*‖z‖))^r:=by
    intro r hr0 hr z hz
    have hf : ContDiffAt ℝ r (vectorProfileJointFunction s₀ s₁ β t j) z:=
      ((hs.of_le (by exact_mod_cast hr)) z hz).contDiffAt (hU.mem_nhds hz)
    have he : iteratedFDeriv ℝ r g z=outer • iteratedFDeriv ℝ r (vectorProfileJointFunction s₀ s₁ β t j) z:=by
      simpa only [g,smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a:=outer) hf
    rw [he,norm_smul,Real.norm_eq_abs]
    have hp : |outer|≤M^r:=
      (le_max_right _ _).trans (le_self_pow₀ hM (by omega))
    have hh:=mul_le_mul hp (hj r hr0 hr z hz) (norm_nonneg _)
      (pow_nonneg (zero_le_one.trans hM) _)
    simpa only [mul_pow,mul_assoc] using hh
  apply exists_exp_common_exponential_jet_envelope N g U hU hg
    (|outer| *B) (|outer| *L) (M*K) D (mul_nonneg (abs_nonneg _) hL)
    (mul_nonneg (zero_le_one.trans hM) (zero_le_one.trans hK)) (zero_le_one.trans hD) ?_ hgj
  intro z hz
  have hh : |vectorProfileJointFunction s₀ s₁ β t j z|≤B+L*‖z‖:=
    hv z ⟨hz.1.le,hz.2.le⟩
  have hmul:=mul_le_mul_of_nonneg_left hh (abs_nonneg outer)
  have hl : outer*vectorProfileJointFunction s₀ s₁ β t j z≤
      |outer| *|vectorProfileJointFunction s₀ s₁ β t j z|:=by
    rw [←abs_mul]
    exact le_abs_self _
  dsimp only [g]
  nlinarith

theorem vectorProfileOuter_dominatedJets_all_theta (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (N j : ℕ) (a b : ℝ) :
    ScalarDominatedJets N (completionLaw n)
      (fun θ p=>vectorProfileRecursion s₀ s₁ β t θ p j 0) (Ioo a b) := by
  obtain ⟨C,D,hC,hD,hj⟩:=exists_vectorProfileJointFunction_common_exp_jets_all_theta
    (n:=n) s₀ s₁ β t N j a b
  exact scalarGaussianLinearDominatedJets_on_bounded_interval N (completionLaw n) (integrable_exp_completion_norm n)
    (ContinuousLinearMap.inl ℝ (Couplings n×ℝ) (Field n))
    (vectorProfileJointFunction s₀ s₁ β t j) a b
    (fun z _=>(contDiff_vectorProfileJointFunction_all_theta s₀ s₁ β t j).contDiffAt) C D (zero_le_one.trans hC) hD hj

theorem vectorProfileOuter_exponential_dominatedJets_all_theta (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (outer : ℝ) (N j : ℕ)
    (a b : ℝ) :
    ScalarDominatedJets N (completionLaw n)
      (fun θ p=>Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p j 0)) (Ioo a b) := by
  obtain ⟨C,D,hC,hD,hj⟩:=exists_vectorProfileJointExponential_exp_jets_all_theta
    (n:=n) s₀ s₁ β t outer N j a b
  exact scalarGaussianLinearDominatedJets_on_bounded_interval N (completionLaw n) (integrable_exp_completion_norm n)
    (ContinuousLinearMap.inl ℝ (Couplings n×ℝ) (Field n))
    (fun z=>Real.exp (outer*vectorProfileJointFunction s₀ s₁ β t j z)) a b
    (fun z _=>(contDiffAt_const.mul (contDiff_vectorProfileJointFunction_all_theta s₀ s₁ β t j).contDiffAt).exp) C D hC hD hj

end QuantitativePaper
