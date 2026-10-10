module
public import QuantitativePaper.VectorProfileGradientScoreMoment
public import QuantitativePaper.VectorProfilePosteriorMomentBound
public import QuantitativePaper.VectorGridProfileMix

@[expose] public section

/-! A depth-independent first profile derivative bound for the actual
restarted dyadic field gradient. The posterior field-history moment is
identified with the true restarted diffusion and is uniformly bounded by
a genuine common Wiener envelope. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileGradientVariationBound (n : ℕ) (β t : ℝ) : ℝ :=
  Real.sqrt (n:ℝ)*(3*((n:ℝ)*((1-t)*β^2)/2)+
    2*Real.sqrt (n:ℝ)*vectorProfilePosteriorMomentBound n β t)

theorem vectorProfileGradientVariationBound_nonneg (n : ℕ) (β t : ℝ) (ht : t≤1) :
    0≤vectorProfileGradientVariationBound n β t := by
  unfold vectorProfileGradientVariationBound
  exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (by positivity)
    (mul_nonneg (by positivity) (vectorProfilePosteriorMomentBound_nonneg n β t ht)))

theorem vectorProfileScheme_clamped (s₀ s₁ : RSBScheme k) (q θ : ℝ)
    (hq : q∈Icc (0:ℝ) 1) (hθ : θ∈Icc (0:ℝ) 1) :
    vectorProfileScheme (vectorClampedScheme s₀ q hq) (vectorClampedScheme s₁ q hq) θ hθ=
      vectorClampedScheme (vectorProfileScheme s₀ s₁ θ hθ) q hq := by
  apply rsbScheme_ext
  · funext i
    cases i with
    | zero => simp only [vectorProfileScheme,vectorProfileMass,RSBScheme.m_zero,mul_zero,add_zero]
    | succ i => simp only [vectorProfileScheme,vectorProfileMass,vectorClampedScheme_mass_succ]
  · rfl

theorem norm_vectorGridProfileTailRecursion_gradient_profile_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ‖deriv (fun φ=>gradient (vectorProfileTailRecursion
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t q φ p
          (vectorDyadicIndex j+3)) x) θ‖≤vectorProfileGradientVariationBound n β t := by
  let d:=vectorDyadicIndex j
  let s₀:=Paper.parisiGridRSBScheme μ d
  let s₁:=Paper.parisiGridRSBScheme ν d
  let C₀:=vectorClampedScheme s₀ q q.property
  let C₁:=vectorClampedScheme s₁ q q.property
  let hθc : θ∈Icc (0:ℝ) 1:=⟨hθ.1.le,hθ.2.le⟩
  have hgrid : ∀i,i≤(d+1+1)+2→C₀.q i=C₁.q i:=fun _ _=>rfl
  have hd:=norm_vectorProfileRecursion_gradient_profile_deriv_le_posterior_moment
    C₀ C₁ hgrid β t ht.le p x (d+2) (by omega) θ hθ
  have hScheme : vectorProfileScheme C₀ C₁ θ hθc=
      vectorClampedScheme (Paper.parisiGridRSBScheme (Paper.parisiMix μ ν θ) d) q q.property := by
    rw [vectorProfileScheme_clamped s₀ s₁ q θ q.property hθc,
      vector_grid_profile_scheme_eq_mix μ ν d θ hθc]
  have hEnv : (fun z : Fin (d+3)→Field n=>vectorProfilePosteriorFieldEnvelope C₀ β t p x (d+2) z)=
      (fun z=>vectorProfilePosteriorFieldEnvelope
        (vectorClampedScheme (Paper.parisiGridRSBScheme (Paper.parisiMix μ ν θ) d) q q.property)
          β t p x (d+2) z) := by
    rw [←hScheme]
    funext z
    unfold vectorProfilePosteriorFieldEnvelope
    rw [vectorHistoryFrom_profileScheme]
  rw [hScheme] at hd
  simp_rw [congrFun hEnv] at hd
  have hm:=integral_vectorClampedGridPosterior_fieldEnvelope_le
    (n:=n) (Paper.parisiMix μ ν θ) j β t hβ ht q p x
  have hb : Real.sqrt (n:ℝ)*(3*((n:ℝ)*((1-t)*β^2)/2)+2*Real.sqrt (n:ℝ)*
      (∫z,vectorProfilePosteriorFieldEnvelope
        (vectorClampedScheme (Paper.parisiGridRSBScheme (Paper.parisiMix μ ν θ) d) q q.property)
          β t p x (d+2) z.1∂vectorTailGaussianPosterior
        (vectorClampedScheme (Paper.parisiGridRSBScheme (Paper.parisiMix μ ν θ) d) q q.property)
          β t p x (d+3)))≤vectorProfileGradientVariationBound n β t := by
    unfold vectorProfileGradientVariationBound
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hm (show 0≤2*Real.sqrt (n:ℝ) by positivity)))
      (Real.sqrt_nonneg _)
  have he : (fun φ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q φ p (d+3)) x)=
      (fun φ=>gradient (vectorProfileRecursion C₀ C₁ β t φ p (d+3)) x) := by
    funext φ
    rw [vectorProfileTailRecursion_eq_clampedProfile s₀ s₁ β t q φ q.property p (by omega)]
  change ‖deriv (fun φ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q φ p (d+3)) x) θ‖≤_
  rw [he]
  exact hd.trans hb

end QuantitativePaper
