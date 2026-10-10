module
public import QuantitativePaper.VectorProfileKernelEnvelopes
public import QuantitativePaper.ScalarGaussianLinearDominatedJets
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

theorem exists_vectorProfileJointExponential_exp_jets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (outer : ℝ) (N j : ℕ) (a b : ℝ) (ha : 0<a) (hb : b<1) :
    ∃C R : ℝ,0≤C ∧ 0≤R ∧ ∀r,r≤N→∀z : ℝ×VectorParameter n,z.1∈Ioo a b→
      ‖iteratedFDeriv ℝ r (fun y=>Real.exp (outer*vectorProfileJointFunction s₀ s₁ β t j y)) z‖≤
        C*Real.exp (R*‖z‖) := by
  let U : Set (ℝ×VectorParameter n):={z|z.1∈Ioo a b}
  have hU : IsOpen U:=isOpen_Ioo.preimage continuous_fst
  obtain ⟨hs,K,D,hK,hD,hj⟩:=vectorProfileJointFunction_smooth_exp_jets_on_cylinder
    (n:=n) s₀ s₁ β t ht N j a b ha hb
  obtain ⟨B,L,hB,hL,hv⟩:=vectorProfileJointFunction_linear_growth (n:=n) s₀ s₁ β t ht j
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
    hv z ⟨(ha.trans hz.1).le,(hz.2.trans hb).le⟩
  have hmul:=mul_le_mul_of_nonneg_left hh (abs_nonneg outer)
  have hl : outer*vectorProfileJointFunction s₀ s₁ β t j z≤
      |outer| *|vectorProfileJointFunction s₀ s₁ β t j z|:=by
    rw [←abs_mul]
    exact le_abs_self _
  dsimp only [g]
  nlinarith

theorem vectorProfileOuter_dominatedJets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (N j : ℕ) (a b : ℝ) (ha : 0<a) (hb : b<1) :
    ScalarDominatedJets N (completionLaw n)
      (fun θ p=>vectorProfileRecursion s₀ s₁ β t θ p j 0) (Ioo a b) := by
  obtain ⟨C,D,hC,hD,hj⟩:=exists_vectorProfileJointFunction_common_exp_jets
    (n:=n) s₀ s₁ β t ht N j a b ha hb
  exact scalarGaussianLinearDominatedJets N (completionLaw n) (integrable_exp_completion_norm n)
    (ContinuousLinearMap.inl ℝ (Couplings n×ℝ) (Field n))
    (vectorProfileJointFunction s₀ s₁ β t j) a b ha hb
    (fun z hz=>contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht j z
      ⟨ha.trans hz.1,hz.2.trans hb⟩) C D (zero_le_one.trans hC) hD hj

theorem vectorProfileOuter_exponential_dominatedJets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (outer : ℝ) (N j : ℕ)
    (a b : ℝ) (ha : 0<a) (hb : b<1) :
    ScalarDominatedJets N (completionLaw n)
      (fun θ p=>Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p j 0)) (Ioo a b) := by
  obtain ⟨C,D,hC,hD,hj⟩:=exists_vectorProfileJointExponential_exp_jets
    (n:=n) s₀ s₁ β t ht outer N j a b ha hb
  exact scalarGaussianLinearDominatedJets N (completionLaw n) (integrable_exp_completion_norm n)
    (ContinuousLinearMap.inl ℝ (Couplings n×ℝ) (Field n))
    (fun z=>Real.exp (outer*vectorProfileJointFunction s₀ s₁ β t j z)) a b ha hb
    (fun z hz=>(contDiffAt_const.mul (contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht j z
      ⟨ha.trans hz.1,hz.2.trans hb⟩)).exp) C D hC hD hj

end QuantitativePaper
