module
public import QuantitativePaper.VectorProfilePosteriorNoiseEnvelope
public import QuantitativePaper.VectorProfilePosteriorRegularity
public import QuantitativePaper.VectorProfilePosteriorDensityBound
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Differentiation of the genuine affine-profile posterior expectation.
The actual normalized density, its literal score and Gaussian exponential
domination discharge every interchange input. The reference coordinates are
kept fixed; no conditional mean or differentiation formula is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integrable_profilePosterior_linear_exp_envelope (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ)
    (A B C D : ℝ) (hA : 0≤A) (hB : 0≤B) :
    Integrable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      (A+B*vectorProfilePosteriorFieldEnvelope s β t p x N z.1)*
        Real.exp (C+D*vectorProfilePosteriorFieldEnvelope s β t p x N z.1))
      (vectorTailGaussianBase n (N+1)) := by
  have hi := ((integrable_exp_vectorProfilePosteriorFieldEnvelope s β t p x N (D+1)).const_mul
    ((A+B)*Real.exp C)).comp_fst (Measure.count : Measure (Configuration n))
  have hmeas : Measurable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      vectorProfilePosteriorFieldEnvelope s β t p x N z.1) :=
    (measurable_vectorProfilePosteriorFieldEnvelope s β t p x N).comp measurable_fst
  apply hi.mono' ((measurable_const.add (measurable_const.mul hmeas)).mul
    (measurable_const.add (measurable_const.mul hmeas)).exp).aestronglyMeasurable
  exact .of_forall fun z=>by
    let E:=vectorProfilePosteriorFieldEnvelope s β t p x N z.1
    have hE : 0≤E:=vectorProfilePosteriorFieldEnvelope_nonneg s β t p x N z.1
    have he : 1≤Real.exp E:=Real.one_le_exp_iff.mpr hE
    have hl : E≤Real.exp E:=by linarith [Real.add_one_le_exp E]
    change ‖(A+B*E)*Real.exp (C+D*E)‖≤(A+B)*Real.exp C*Real.exp ((D+1)*E)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (add_nonneg hA (mul_nonneg hB hE))
      (Real.exp_pos _).le)]
    calc
      _ ≤ ((A+B)*Real.exp E)*Real.exp (C+D*E) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have ha:=mul_le_mul_of_nonneg_left he hA
        have hb:=mul_le_mul_of_nonneg_left hl hB
        nlinarith
      _ = _ := by
        rw [mul_assoc,←Real.exp_add,show E+(C+D*E)=C+(D+1)*E by ring,Real.exp_add]
        ring

def vectorProfilePosteriorMean (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (d : Configuration n→ℝ) (θ : ℝ) : ℝ :=
  ∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*d z.2
    ∂vectorTailGaussianBase n (N+1)

theorem vectorProfilePosteriorMean_eq_conditionalMean (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) (p : Couplings n×ℝ)
    (x : Field n) (N : ℕ) (hN : N+1≤k+2) (d : Configuration n→ℝ) :
    vectorProfilePosteriorMean s₀ s₁ β t p x N d θ=
      vectorConditionalMean (vectorProfileScheme s₀ s₁ θ hθ) β t p (fun _=>0) d (N+1) 0 x := by
  unfold vectorProfilePosteriorMean
  simp_rw [vectorProfilePosteriorLogDensity_eq_scheme s₀ s₁ β t θ hθ p x N hN]
  exact integral_vectorTailPosterior_exp_spin _ β t p x (N+1) hN d

theorem hasDerivAt_vectorProfilePosteriorMean (s₀ s₁ : RSBScheme k)
    (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i) (β t : ℝ) (ht : t≤1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (d : Configuration n→ℝ) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    Integrable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ*d z.2)
      (vectorTailGaussianBase n (N+1)) ∧
    HasDerivAt (vectorProfilePosteriorMean s₀ s₁ β t p x N d)
      (∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)*
        deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ*d z.2
        ∂vectorTailGaussianBase n (N+1)) θ := by
  let M:=∑σ : Configuration n,|d σ|
  let B:=(n:ℝ)*((1-t)*β^2)/2
  let H:=Real.sqrt (n:ℝ)
  let E:=vectorProfilePosteriorFieldEnvelope s₀ β t p x N
  let F:=fun φ (z : (Fin (N+1)→Field n)×Configuration n)=>
    Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)*d z.2
  let F':=fun φ (z : (Fin (N+1)→Field n)×Configuration n)=>
    Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)*
      deriv (fun ψ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N ψ z) φ*d z.2
  let bound:=fun z : (Fin (N+1)→Field n)×Configuration n=>
    M*((3*B+2*H*E z.1)*Real.exp (B+2*H*E z.1))
  have hB : 0≤B:=by dsimp only [B];positivity
  have hM : 0≤M:=Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hd (σ : Configuration n) : |d σ|≤M:=
    Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ)
  have hmeas (φ : ℝ) : Measurable (F φ):=
    (measurable_vectorProfilePosteriorLogDensity s₀ s₁ β t φ p x N).exp.mul
      ((measurable_of_finite d).comp measurable_snd)
  have hdm (φ : ℝ) : Measurable (F' φ):=
    ((measurable_vectorProfilePosteriorLogDensity s₀ s₁ β t φ p x N).exp.mul
      (measurable_vectorProfilePosteriorLogDensity_deriv s₀ s₁ β t φ p x N)).mul
      ((measurable_of_finite d).comp measurable_snd)
  have hi : Integrable (F θ) (vectorTailGaussianBase n (N+1)) := by
    have he := integrable_vectorTailPosterior_exp (vectorProfileScheme s₀ s₁ θ
      ⟨hθ.1.le,hθ.2.le⟩) β t p x (N+1) hN
    simp_rw [←vectorProfilePosteriorLogDensity_eq_scheme s₀ s₁ β t θ ⟨hθ.1.le,hθ.2.le⟩ p x N hN] at he
    apply (he.const_mul M).mono' (hmeas θ).aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖Real.exp _*d z.2‖≤M*Real.exp _
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      nlinarith [hd z.2,Real.exp_pos (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)]
  have hb : Integrable bound (vectorTailGaussianBase n (N+1)):=
    (integrable_profilePosterior_linear_exp_envelope s₀ β t p x N (3*B) (2*H) B (2*H)
      (mul_nonneg (by norm_num) hB) (by dsimp only [H];positivity)).const_mul M
  have hdiff (z) (φ : ℝ) : HasDerivAt (fun ψ=>F ψ z) (F' φ z) φ := by
    have hh:=(hasDerivAt_vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)
    rw [←hh.deriv] at hh
    exact hh.exp.mul_const (d z.2)
  have hbound (z) (φ : ℝ) (hφ : φ∈Ioo (0:ℝ) 1) : ‖F' φ z‖≤bound z := by
    have hs:=vectorProfilePosteriorLogDensity_deriv_bound s₀ s₁ hgrid β t φ ht hφ p x N hN z
    have hden:=vectorProfilePosteriorLogDensity_upper s₀ s₁ β t φ ht ⟨hφ.1.le,hφ.2.le⟩ p x N hN z
    have hdens:=Real.exp_le_exp.mpr hden
    have hs0 : 0≤3*B+2*H*E z.1:=add_nonneg (mul_nonneg (by norm_num) hB)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (vectorProfilePosteriorFieldEnvelope_nonneg s₀ β t p x N z.1))
    dsimp only [F',bound]
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.exp (B+2*H*E z.1)*(3*B+2*H*E z.1))*M :=
        mul_le_mul (mul_le_mul hdens hs (abs_nonneg _) (Real.exp_pos _).le) (hd z.2)
          (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hs0)
      _ = _ := by ring
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (isOpen_Ioo.mem_nhds hθ)
    (.of_forall fun φ=>(hmeas φ).aestronglyMeasurable) hi (hdm θ).aestronglyMeasurable
    (.of_forall hbound) hb (.of_forall fun z φ _=>hdiff z φ)

end QuantitativePaper
