module
public import QuantitativePaper.VectorProfilePosteriorSecondRegularity

@[expose] public section

/-! Genuine second differentiation of the normalized posterior integral.
The stated second-score bound is used only in this generic calculus helper;
the clamped-grid model supplies it from the actual restarted PDE telescope. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem hasDerivAt_vectorProfilePosteriorMean_deriv_of_second_score_bound
    (s₀ s₁ : RSBScheme k) (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i)
    (β t : ℝ) (ht : t≤1) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (d : Configuration n→ℝ) (Q : ℝ) (hQ : 0≤Q)
    (hsecond : ∀φ∈Ioo (0:ℝ) 1,∀z : (Fin (N+1)→Field n)×Configuration n,
      |deriv (deriv (fun ψ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N ψ z)) φ|≤Q)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    Integrable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        ((deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
          deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ)*d z.2)
      (vectorTailGaussianBase n (N+1)) ∧
    HasDerivAt (deriv (vectorProfilePosteriorMean s₀ s₁ β t p x N d))
      (∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        ((deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ)^2+
          deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ)*d z.2
        ∂vectorTailGaussianBase n (N+1)) θ := by
  let B:=(n:ℝ)*((1-t)*β^2)/2
  let H:=Real.sqrt (n:ℝ)
  let M:=∑σ : Configuration n,|d σ|
  let E:=vectorProfilePosteriorFieldEnvelope s₀ β t p x N
  let L:=fun φ (z : (Fin (N+1)→Field n)×Configuration n)=>
    vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z
  let F:=fun φ (z : (Fin (N+1)→Field n)×Configuration n)=>
    Real.exp (L φ z)*deriv (fun ψ=>L ψ z) φ*d z.2
  let F':=fun φ (z : (Fin (N+1)→Field n)×Configuration n)=>
    Real.exp (L φ z)*((deriv (fun ψ=>L ψ z) φ)^2+deriv (deriv (fun ψ=>L ψ z)) φ)*d z.2
  let C:=M*(2*Real.exp (4*B)+Q*Real.exp B)
  let bound:=fun z : (Fin (N+1)→Field n)×Configuration n=>C*Real.exp (4*H*E z.1)
  have hB : 0≤B:=by dsimp only [B];positivity
  have hH : 0≤H:=Real.sqrt_nonneg _
  have hM : 0≤M:=Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hd (σ : Configuration n) : |d σ|≤M:=
    Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ)
  have hfMeas (φ : ℝ) : Measurable (F φ):=
    ((measurable_vectorProfilePosteriorLogDensity s₀ s₁ β t φ p x N).exp.mul
      (measurable_vectorProfilePosteriorLogDensity_deriv s₀ s₁ β t φ p x N)).mul
      ((measurable_of_finite d).comp measurable_snd)
  have hf'Meas (φ : ℝ) : Measurable (F' φ):=
    ((measurable_vectorProfilePosteriorLogDensity s₀ s₁ β t φ p x N).exp.mul
      ((measurable_vectorProfilePosteriorLogDensity_deriv s₀ s₁ β t φ p x N).pow_const 2 |>.add
        (measurable_vectorProfilePosteriorLogDensity_second_deriv s₀ s₁ β t φ p x N))).mul
      ((measurable_of_finite d).comp measurable_snd)
  have hi : Integrable (F θ) (vectorTailGaussianBase n (N+1)):=
    (hasDerivAt_vectorProfilePosteriorMean s₀ s₁ hgrid β t ht p x N hN d θ hθ).1
  have hb : Integrable bound (vectorTailGaussianBase n (N+1)):=
    ((integrable_exp_vectorProfilePosteriorFieldEnvelope s₀ β t p x N (4*H)).const_mul C).comp_fst
      (Measure.count : Measure (Configuration n))
  have hdiff (z) (φ : ℝ) : HasDerivAt (fun ψ=>F ψ z) (F' φ z) φ := by
    have h₁:=hasDerivAt_vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z
    rw [←h₁.deriv] at h₁
    have h₂:=hasDerivAt_vectorProfilePosteriorLogDensity_deriv s₀ s₁ β t p x N φ z
    rw [←h₂.deriv] at h₂
    convert (h₁.exp.mul h₂).mul_const (d z.2) using 1
    dsimp only [F',L]
    ring
  have hbound (z) (φ : ℝ) (hφ : φ∈Ioo (0:ℝ) 1) : ‖F' φ z‖≤bound z := by
    let S:=3*B+2*H*E z.1
    let D:=B+2*H*E z.1
    have hE : 0≤E z.1:=vectorProfilePosteriorFieldEnvelope_nonneg s₀ β t p x N z.1
    have hS : 0≤S:=by dsimp only [S];positivity
    have hscore : |deriv (fun ψ=>L ψ z) φ|≤S:=
      vectorProfilePosteriorLogDensity_deriv_bound s₀ s₁ hgrid β t φ ht hφ p x N hN z
    have hden : Real.exp (L φ z)≤Real.exp D:=Real.exp_le_exp.mpr
      (vectorProfilePosteriorLogDensity_upper s₀ s₁ β t φ ht ⟨hφ.1.le,hφ.2.le⟩ p x N hN z)
    have hscore2 : (deriv (fun ψ=>L ψ z) φ)^2≤S^2:=by
      rw [←sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hS).mpr hscore
    have hpow : S^2≤2*Real.exp S:=by
      have hh:=Real.pow_div_factorial_le_exp S hS 2
      norm_num at hh
      linarith
    have hsum : |(deriv (fun ψ=>L ψ z) φ)^2+deriv (deriv (fun ψ=>L ψ z)) φ|≤S^2+Q:=
      (abs_add_le _ _).trans (add_le_add (by rw [abs_of_nonneg (sq_nonneg _)];exact hscore2)
        (hsecond φ hφ z))
    dsimp only [F',bound]
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _≤Real.exp D*(S^2+Q)*M:=mul_le_mul
        (mul_le_mul hden hsum (abs_nonneg _) (Real.exp_pos _).le) (hd z.2)
        (abs_nonneg _) (by positivity)
      _≤Real.exp D*(2*Real.exp S+Q)*M:=by gcongr
      _=M*(2*Real.exp (4*B+4*H*E z.1)+Q*Real.exp (B+2*H*E z.1)):=by
        have hDS : Real.exp D*Real.exp S=Real.exp (4*B+4*H*E z.1):=by
          rw [←Real.exp_add]
          congr 1
          dsimp only [S,D]
          ring
        calc
          _=M*(2*(Real.exp D*Real.exp S)+Q*Real.exp D):=by ring
          _=_:=by rw [hDS]
      _≤M*(2*Real.exp (4*B+4*H*E z.1)+Q*Real.exp (B+4*H*E z.1)):=by gcongr;nlinarith
      _=_:=by dsimp only [C];rw [Real.exp_add,Real.exp_add];ring
  obtain ⟨hi',hd'⟩:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (isOpen_Ioo.mem_nhds hθ)
    (.of_forall fun φ=>(hfMeas φ).aestronglyMeasurable) hi (hf'Meas θ).aestronglyMeasurable
    (.of_forall hbound) hb (.of_forall fun z φ _=>hdiff z φ)
  have he : deriv (vectorProfilePosteriorMean s₀ s₁ β t p x N d)=ᶠ[𝓝 θ]
      (fun φ=>∫z,F φ z∂vectorTailGaussianBase n (N+1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    exact (hasDerivAt_vectorProfilePosteriorMean s₀ s₁ hgrid β t ht p x N hN d φ hφ).2.deriv
  exact ⟨hi',hd'.congr_of_eventuallyEq he⟩

end QuantitativePaper
