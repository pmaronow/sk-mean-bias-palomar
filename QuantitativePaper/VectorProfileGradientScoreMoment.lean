module
public import QuantitativePaper.VectorProfileGradientFirstVariation

@[expose] public section

/-! Quantitative first profile-gradient control in terms of the genuine
posterior field-displacement moment. The moment is finite and is identified
with the actual normalized posterior measure, not assumed to be a law. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integrable_vectorProfilePosterior_exp_fieldEnvelope (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2) :
    Integrable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1)
      (vectorTailGaussianBase n (N+1)) := by
  let B:=(n:ℝ)*((1-t)*β^2)/2
  let H:=2*Real.sqrt (n:ℝ)
  have hi:=integrable_profilePosterior_linear_exp_envelope s₀ β t p x N 0 1 B H le_rfl zero_le_one
  simp only [zero_add,one_mul] at hi
  have hm : Measurable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1) :=
    (measurable_vectorProfilePosteriorFieldEnvelope s₀ β t p x N).comp measurable_fst
  apply hi.mono' (((measurable_vectorProfilePosteriorLogDensity s₀ s₁ β t θ p x N).exp).mul hm).aestronglyMeasurable
  exact .of_forall fun z=>by
    change ‖Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
      vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (vectorProfilePosteriorFieldEnvelope_nonneg s₀ β t p x N z.1))]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (vectorProfilePosteriorLogDensity_upper s₀ s₁ β t θ ht hθ p x N hN z))
      (vectorProfilePosteriorFieldEnvelope_nonneg s₀ β t p x N z.1)).trans_eq (mul_comm _ _)

theorem vectorProfilePosterior_exp_fieldEnvelope_eq_posterior (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n)
    (N : ℕ) (hN : N+1≤k+2) :
    (∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
      vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1
      ∂vectorTailGaussianBase n (N+1))=
    ∫z,vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1
      ∂vectorTailGaussianPosterior (vectorProfileScheme s₀ s₁ θ hθ) β t p x (N+1) := by
  rw [vectorTailGaussianPosterior_eq_exp_density _ β t p x (N+1) hN,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_vectorTailPosteriorLogDensity _ β t p x (N+1)).exp.ennreal_ofReal)
      (.of_forall fun z=>ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,
    ←vectorProfilePosteriorLogDensity_eq_scheme s₀ s₁ β t θ hθ p x N hN]

theorem norm_vectorProfileRecursion_gradient_profile_deriv_le_posterior_moment
    (s₀ s₁ : RSBScheme k) (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i)
    (β t : ℝ) (ht : t≤1) (p : Couplings n×ℝ) (x : Field n)
    (N : ℕ) (hN : N+1≤k+2) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ‖deriv (fun φ=>gradient (vectorProfileRecursion s₀ s₁ β t φ p (N+1)) x) θ‖≤
      Real.sqrt (n:ℝ)*(3*((n:ℝ)*((1-t)*β^2)/2)+2*Real.sqrt (n:ℝ)*
        (∫z,vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1
          ∂vectorTailGaussianPosterior (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩)
            β t p x (N+1))) := by
  let B:=(n:ℝ)*((1-t)*β^2)/2
  let H:=Real.sqrt (n:ℝ)
  let L:=vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ
  let E:=fun z : (Fin (N+1)→Field n)×Configuration n=>
    vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1
  have hi:=integrable_vectorTailPosterior_exp (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩)
    β t p x (N+1) hN
  simp_rw [←vectorProfilePosteriorLogDensity_eq_scheme s₀ s₁ β t θ ⟨hθ.1.le,hθ.2.le⟩ p x N hN] at hi
  have hie:=integrable_vectorProfilePosterior_exp_fieldEnvelope s₀ s₁ β t θ ht
    ⟨hθ.1.le,hθ.2.le⟩ p x N hN
  have hscore : Integrable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      Real.exp (L z)*|deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ|)
      (vectorTailGaussianBase n (N+1)) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_vectorProfilePosteriorScore s₀ s₁ hgrid β t ht p x N hN θ hθ).norm
  have hsc:=integral_mono hscore ((hi.const_mul (3*B)).add (hie.const_mul (2*H)))
    (fun z=>by
      have hh:=mul_le_mul_of_nonneg_left (vectorProfilePosteriorLogDensity_deriv_bound s₀ s₁ hgrid
        β t θ ht hθ p x N hN z) (Real.exp_pos (L z)).le
      change Real.exp (L z)*|deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ|≤
        3*B*Real.exp (L z)+2*H*(Real.exp (L z)*E z)
      exact hh.trans_eq (by ring))
  change (∫z,Real.exp (L z)*|deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ|
      ∂vectorTailGaussianBase n (N+1)) ≤
    ∫z,3*B*Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)+
      2*H*(Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1)
      ∂vectorTailGaussianBase n (N+1) at hsc
  rw [integral_add (hi.const_mul (3*B)) (hie.const_mul (2*H)),
    integral_const_mul,integral_const_mul,
    integral_exp_vectorProfilePosteriorLogDensity s₀ s₁ β t θ ⟨hθ.1.le,hθ.2.le⟩ p x N hN,
    mul_one,vectorProfilePosterior_exp_fieldEnvelope_eq_posterior s₀ s₁ β t θ
      ⟨hθ.1.le,hθ.2.le⟩ p x N hN] at hsc
  exact (norm_vectorProfileRecursion_gradient_profile_deriv_le_score s₀ s₁ hgrid β t ht p x N hN θ hθ).trans
    (mul_le_mul_of_nonneg_left hsc (Real.sqrt_nonneg _))

end QuantitativePaper
