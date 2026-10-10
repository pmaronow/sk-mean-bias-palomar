module
public import QuantitativePaper.VectorProfileGradientSecondVariation
public import QuantitativePaper.VectorProfileGradientScoreMoment

@[expose] public section

/-! Second profile-gradient control by the actual posterior displacement
second moment. The Gaussian reference and normalized density are explicit. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integrable_vectorProfilePosterior_exp_fieldEnvelope_sq (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2) :
    Integrable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        (vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1)^2)
      (vectorTailGaussianBase n (N+1)) := by
  let B:=(n:ℝ)*((1-t)*β^2)/2
  let H:=2*Real.sqrt (n:ℝ)
  have hi:=((integrable_exp_vectorProfilePosteriorFieldEnvelope s₀ β t p x N (H+1)).const_mul
    (2*Real.exp B)).comp_fst (Measure.count : Measure (Configuration n))
  have hm : Measurable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1) :=
    (measurable_vectorProfilePosteriorFieldEnvelope s₀ β t p x N).comp measurable_fst
  apply hi.mono' (((measurable_vectorProfilePosteriorLogDensity s₀ s₁ β t θ p x N).exp).mul
    (hm.pow_const 2)).aestronglyMeasurable
  exact .of_forall fun z=>by
    let E:=vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1
    have hE : 0≤E:=vectorProfilePosteriorFieldEnvelope_nonneg s₀ β t p x N z.1
    have hp : E^2≤2*Real.exp E:=by
      have hh:=Real.pow_div_factorial_le_exp E hE 2
      norm_num at hh
      linarith
    have he:=Real.exp_le_exp.mpr
      (vectorProfilePosteriorLogDensity_upper s₀ s₁ β t θ ht hθ p x N hN z)
    change ‖Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*E^2‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc
      _≤Real.exp (B+H*E)*(2*Real.exp E):=mul_le_mul he hp (sq_nonneg _) (Real.exp_pos _).le
      _=2*Real.exp B*Real.exp ((H+1)*E):=by rw [Real.exp_add,add_mul,one_mul,Real.exp_add];ring

theorem vectorProfilePosterior_exp_fieldEnvelope_sq_eq_posterior (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n)
    (N : ℕ) (hN : N+1≤k+2) :
    (∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
      (vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1)^2
      ∂vectorTailGaussianBase n (N+1))=
    ∫z,(vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1)^2
      ∂vectorTailGaussianPosterior (vectorProfileScheme s₀ s₁ θ hθ) β t p x (N+1) := by
  rw [vectorTailGaussianPosterior_eq_exp_density _ β t p x (N+1) hN,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_vectorTailPosteriorLogDensity _ β t p x (N+1)).exp.ennreal_ofReal)
      (.of_forall fun z=>ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,
    ←vectorProfilePosteriorLogDensity_eq_scheme s₀ s₁ β t θ hθ p x N hN]

theorem norm_vectorProfileRecursion_gradient_second_profile_deriv_le_posterior_moment
    (s₀ s₁ : RSBScheme k) (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i)
    (β t : ℝ) (ht : t≤1) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (Q : ℝ) (hQ : 0≤Q)
    (hsecond : ∀φ∈Ioo (0:ℝ) 1,∀z : (Fin (N+1)→Field n)×Configuration n,
      |deriv (deriv (fun ψ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N ψ z)) φ|≤Q)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ‖deriv (deriv (fun φ=>gradient (vectorProfileRecursion s₀ s₁ β t φ p (N+1)) x)) θ‖≤
      Real.sqrt (n:ℝ)*(18*((n:ℝ)*((1-t)*β^2)/2)^2+Q+8*(n:ℝ)*
        (∫z,(vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1)^2
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
  have hie:=integrable_vectorProfilePosterior_exp_fieldEnvelope_sq s₀ s₁ β t θ ht
    ⟨hθ.1.le,hθ.2.le⟩ p x N hN
  have hscore : Integrable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      Real.exp (L z)*|(deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
        deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ|)
      (vectorTailGaussianBase n (N+1)) := by
    simpa only [mul_one,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
      (hasDerivAt_vectorProfilePosteriorMean_deriv_of_second_score_bound s₀ s₁ hgrid β t ht
        p x N hN (fun _=>1) Q hQ hsecond θ hθ).1.norm
  have hsc:=integral_mono hscore ((hi.const_mul (18*B^2+Q)).add (hie.const_mul (8*(n:ℝ))))
    (fun z=>by
      have hh:=vectorProfilePosteriorLogDensity_deriv_bound s₀ s₁ hgrid β t θ ht hθ p x N hN z
      have hn:=(vectorProfilePosteriorFieldEnvelope_nonneg s₀ β t p x N z.1)
      have hB : 0≤B:=by dsimp only [B];positivity
      have hH : H^2=(n:ℝ):=Real.sq_sqrt (Nat.cast_nonneg _)
      have hs : (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2≤
          (3*B+2*H*E z)^2 := by
        rw [←sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
      have hy : (3*B+2*H*E z)^2≤18*B^2+8*(n:ℝ)*(E z)^2 := by
        nlinarith [sq_nonneg (3*B-2*H*E z)]
      have ha : |(deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
          deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ|≤
          18*B^2+8*(n:ℝ)*(E z)^2+Q := (abs_add_le
        ((deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2)
        (deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ)).trans
          (add_le_add (by
            rw [abs_of_nonneg (sq_nonneg (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ))]
            exact hs.trans hy) (hsecond θ hθ z))
      have hm:=mul_le_mul_of_nonneg_left ha (Real.exp_pos (L z)).le
      change Real.exp (L z)*|_|≤(18*B^2+Q)*Real.exp (L z)+8*(n:ℝ)*(Real.exp (L z)*(E z)^2)
      exact hm.trans_eq (by ring))
  change (∫z,Real.exp (L z)*|_|∂vectorTailGaussianBase n (N+1))≤
    ∫z,(18*B^2+Q)*Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)+
      8*(n:ℝ)*(Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        (vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1)^2)
      ∂vectorTailGaussianBase n (N+1) at hsc
  rw [integral_add (hi.const_mul _) (hie.const_mul _),integral_const_mul,integral_const_mul,
    integral_exp_vectorProfilePosteriorLogDensity s₀ s₁ β t θ ⟨hθ.1.le,hθ.2.le⟩ p x N hN,
    mul_one,vectorProfilePosterior_exp_fieldEnvelope_sq_eq_posterior s₀ s₁ β t θ
      ⟨hθ.1.le,hθ.2.le⟩ p x N hN] at hsc
  exact (norm_vectorProfileRecursion_gradient_second_profile_deriv_le_score s₀ s₁ hgrid β t ht
    p x N hN Q hQ hsecond θ hθ).trans (mul_le_mul_of_nonneg_left hsc (Real.sqrt_nonneg _))

end QuantitativePaper
