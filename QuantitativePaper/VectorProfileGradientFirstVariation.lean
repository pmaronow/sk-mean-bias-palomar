module
public import QuantitativePaper.VectorProfilePosteriorDifferentiation
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! The actual finite profile derivative of the field gradient is the
literal normalized-posterior score/spin pairing. All interchange inputs are
proved by the actual Gaussian domination package. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfilePosteriorSpinMean (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (θ : ℝ) : Field n :=
  WithLp.toLp 2 (fun i=>vectorProfilePosteriorMean s₀ s₁ β t p x N (fun σ=>Paper.spinSign (σ i)) θ)

theorem vectorProfilePosteriorSpinMean_eq_gradient (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n)
    (N : ℕ) (hN : N+1≤k+2) :
    vectorProfilePosteriorSpinMean s₀ s₁ β t p x N θ=
      gradient (vectorProfileRecursion s₀ s₁ β t θ p (N+1)) x := by
  rw [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ p,
    ←vectorMagnetization_eq_gradient]
  apply PiLp.ext
  intro i
  change vectorProfilePosteriorMean s₀ s₁ β t p x N (fun σ=>Paper.spinSign (σ i)) θ=_
  rw [vectorProfilePosteriorMean_eq_conditionalMean s₀ s₁ β t θ hθ p x N hN,
    vectorConditionalMean_zero_eq_response]
  rfl

theorem integrable_vectorProfilePosteriorScore (s₀ s₁ : RSBScheme k)
    (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i) (β t : ℝ) (ht : t≤1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    Integrable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)
      (vectorTailGaussianBase n (N+1)) := by
  simpa only [mul_one] using
    (hasDerivAt_vectorProfilePosteriorMean s₀ s₁ hgrid β t ht p x N hN (fun _=>1) θ hθ).1

theorem hasDerivAt_vectorProfilePosteriorSpinMean (s₀ s₁ : RSBScheme k)
    (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i) (β t : ℝ) (ht : t≤1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    HasDerivAt (vectorProfilePosteriorSpinMean s₀ s₁ β t p x N)
      (∫z,(Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ) • spinVector z.2
        ∂vectorTailGaussianBase n (N+1)) θ := by
  let f:=fun φ (i : Fin n)=>vectorProfilePosteriorMean s₀ s₁ β t p x N (fun σ=>Paper.spinSign (σ i)) φ
  let v:=fun i : Fin n=>∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
    deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ*Paper.spinSign (z.2 i)
    ∂vectorTailGaussianBase n (N+1)
  have hd : HasDerivAt (fun φ=>f φ) v θ:=hasDerivAt_pi.mpr fun i=>
    (hasDerivAt_vectorProfilePosteriorMean s₀ s₁ hgrid β t ht p x N hN
      (fun σ=>Paper.spinSign (σ i)) θ hθ).2
  have hld:=(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)).symm.hasFDerivAt.comp_hasDerivAt θ hd
  have he : WithLp.toLp 2 v=(∫z,(Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
      deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ) • spinVector z.2
      ∂vectorTailGaussianBase n (N+1)) := by
    apply PiLp.ext
    intro i
    rw [eval_integral_piLp]
    · rfl
    · intro l
      simpa only [PiLp.smul_apply,spinVector,smul_eq_mul] using
        (hasDerivAt_vectorProfilePosteriorMean s₀ s₁ hgrid β t ht p x N hN
          (fun σ=>Paper.spinSign (σ l)) θ hθ).1
  rw [←he]
  exact hld

theorem hasDerivAt_vectorProfileRecursion_gradient_profile (s₀ s₁ : RSBScheme k)
    (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i) (β t : ℝ) (ht : t≤1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun φ=>gradient (vectorProfileRecursion s₀ s₁ β t φ p (N+1)) x)
      (∫z,(Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ) • spinVector z.2
        ∂vectorTailGaussianBase n (N+1)) θ := by
  have he : (fun φ=>gradient (vectorProfileRecursion s₀ s₁ β t φ p (N+1)) x)=ᶠ[𝓝 θ]
      vectorProfilePosteriorSpinMean s₀ s₁ β t p x N := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    exact (vectorProfilePosteriorSpinMean_eq_gradient s₀ s₁ β t φ ⟨hφ.1.le,hφ.2.le⟩ p x N hN).symm
  exact (hasDerivAt_vectorProfilePosteriorSpinMean s₀ s₁ hgrid β t ht p x N hN θ hθ).congr_of_eventuallyEq he

theorem norm_vectorProfileRecursion_gradient_profile_deriv_le_score (s₀ s₁ : RSBScheme k)
    (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i) (β t : ℝ) (ht : t≤1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ‖deriv (fun φ=>gradient (vectorProfileRecursion s₀ s₁ β t φ p (N+1)) x) θ‖≤
      Real.sqrt (n:ℝ)*(∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        |deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ|
        ∂vectorTailGaussianBase n (N+1)) := by
  rw [(hasDerivAt_vectorProfileRecursion_gradient_profile s₀ s₁ hgrid β t ht p x N hN θ hθ).deriv]
  apply (norm_integral_le_integral_norm _).trans_eq
  simp_rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),norm_spinVector]
  rw [integral_mul_const,mul_comm]

end QuantitativePaper
