module
public import QuantitativePaper.VectorProfilePosteriorSecondDifferentiation
public import QuantitativePaper.VectorProfileGradientFirstVariation

@[expose] public section

/-! Actual second differentiation of the posterior spin mean and the
field gradient. The generic second-score bound is discharged for dyadic
profiles by the restarted second-variation telescope. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem deriv_vectorProfilePosteriorSpinMean_eq_pi (s₀ s₁ : RSBScheme k)
    (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i) (β t : ℝ) (ht : t≤1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    deriv (vectorProfilePosteriorSpinMean s₀ s₁ β t p x N) θ=
      WithLp.toLp 2 (fun i=>deriv (vectorProfilePosteriorMean s₀ s₁ β t p x N
        (fun σ=>Paper.spinSign (σ i))) θ) := by
  have hd : HasDerivAt
      (fun φ (i : Fin n)=>vectorProfilePosteriorMean s₀ s₁ β t p x N
        (fun σ=>Paper.spinSign (σ i)) φ)
      (fun i=>deriv (vectorProfilePosteriorMean s₀ s₁ β t p x N
        (fun σ=>Paper.spinSign (σ i))) θ) θ :=
    hasDerivAt_pi.mpr fun i=>by
      have hh:=(hasDerivAt_vectorProfilePosteriorMean s₀ s₁ hgrid β t ht p x N hN
        (fun σ=>Paper.spinSign (σ i)) θ hθ).2
      rw [←hh.deriv] at hh
      exact hh
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)).symm.hasFDerivAt.comp_hasDerivAt θ hd).deriv

theorem hasDerivAt_vectorProfilePosteriorSpinMean_deriv_of_second_score_bound
    (s₀ s₁ : RSBScheme k) (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i)
    (β t : ℝ) (ht : t≤1) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (Q : ℝ) (hQ : 0≤Q)
    (hsecond : ∀φ∈Ioo (0:ℝ) 1,∀z : (Fin (N+1)→Field n)×Configuration n,
      |deriv (deriv (fun ψ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N ψ z)) φ|≤Q)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    HasDerivAt (deriv (vectorProfilePosteriorSpinMean s₀ s₁ β t p x N))
      (∫z,(Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        ((deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
          deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ)) •
            spinVector z.2∂vectorTailGaussianBase n (N+1)) θ := by
  let v:=fun i : Fin n=>∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
    ((deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
      deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ)*
        Paper.spinSign (z.2 i)∂vectorTailGaussianBase n (N+1)
  have hd : HasDerivAt (fun φ (i : Fin n)=>deriv
      (vectorProfilePosteriorMean s₀ s₁ β t p x N (fun σ=>Paper.spinSign (σ i))) φ) v θ :=
    hasDerivAt_pi.mpr fun i=>
      (hasDerivAt_vectorProfilePosteriorMean_deriv_of_second_score_bound s₀ s₁ hgrid β t ht
        p x N hN (fun σ=>Paper.spinSign (σ i)) Q hQ hsecond θ hθ).2
  have hld:=(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)).symm.hasFDerivAt.comp_hasDerivAt θ hd
  have he : WithLp.toLp 2 v=(∫z,(Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
      ((deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
        deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ)) •
          spinVector z.2∂vectorTailGaussianBase n (N+1)) := by
    apply PiLp.ext
    intro i
    rw [eval_integral_piLp]
    · rfl
    · intro l
      simpa only [PiLp.smul_apply,spinVector,smul_eq_mul] using
        (hasDerivAt_vectorProfilePosteriorMean_deriv_of_second_score_bound s₀ s₁ hgrid β t ht
          p x N hN (fun σ=>Paper.spinSign (σ l)) Q hQ hsecond θ hθ).1
  have he' : deriv (vectorProfilePosteriorSpinMean s₀ s₁ β t p x N)=ᶠ[𝓝 θ]
      (fun φ=>WithLp.toLp 2 (fun i=>deriv (vectorProfilePosteriorMean s₀ s₁ β t p x N
        (fun σ=>Paper.spinSign (σ i))) φ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    exact deriv_vectorProfilePosteriorSpinMean_eq_pi s₀ s₁ hgrid β t ht p x N hN φ hφ
  rw [←he]
  exact hld.congr_of_eventuallyEq he'

theorem hasDerivAt_vectorProfileRecursion_gradient_profile_deriv_of_second_score_bound
    (s₀ s₁ : RSBScheme k) (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i)
    (β t : ℝ) (ht : t≤1) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (Q : ℝ) (hQ : 0≤Q)
    (hsecond : ∀φ∈Ioo (0:ℝ) 1,∀z : (Fin (N+1)→Field n)×Configuration n,
      |deriv (deriv (fun ψ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N ψ z)) φ|≤Q)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    HasDerivAt (deriv (fun φ=>gradient (vectorProfileRecursion s₀ s₁ β t φ p (N+1)) x))
      (∫z,(Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        ((deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
          deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ)) •
            spinVector z.2∂vectorTailGaussianBase n (N+1)) θ := by
  have he : (fun φ=>gradient (vectorProfileRecursion s₀ s₁ β t φ p (N+1)) x)=ᶠ[𝓝 θ]
      vectorProfilePosteriorSpinMean s₀ s₁ β t p x N := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    exact (vectorProfilePosteriorSpinMean_eq_gradient s₀ s₁ β t φ ⟨hφ.1.le,hφ.2.le⟩ p x N hN).symm
  exact (hasDerivAt_vectorProfilePosteriorSpinMean_deriv_of_second_score_bound
    s₀ s₁ hgrid β t ht p x N hN Q hQ hsecond θ hθ).congr_of_eventuallyEq he.deriv

theorem norm_vectorProfileRecursion_gradient_second_profile_deriv_le_score
    (s₀ s₁ : RSBScheme k) (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i)
    (β t : ℝ) (ht : t≤1) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (Q : ℝ) (hQ : 0≤Q)
    (hsecond : ∀φ∈Ioo (0:ℝ) 1,∀z : (Fin (N+1)→Field n)×Configuration n,
      |deriv (deriv (fun ψ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N ψ z)) φ|≤Q)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ‖deriv (deriv (fun φ=>gradient (vectorProfileRecursion s₀ s₁ β t φ p (N+1)) x)) θ‖≤
      Real.sqrt (n:ℝ)*(∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        |(deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
          deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ|
        ∂vectorTailGaussianBase n (N+1)) := by
  rw [(hasDerivAt_vectorProfileRecursion_gradient_profile_deriv_of_second_score_bound
    s₀ s₁ hgrid β t ht p x N hN Q hQ hsecond θ hθ).deriv]
  apply (norm_integral_le_integral_norm _).trans_eq
  simp_rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),norm_spinVector]
  rw [integral_mul_const,mul_comm]

end QuantitativePaper
