module
public import QuantitativePaper.VectorProfileGradientSecondScoreMoment
public import QuantitativePaper.VectorGridProfilePosteriorSecondScore
public import QuantitativePaper.VectorProfilePosteriorPowerMoments

@[expose] public section

/-! The actual field gradient has a depth-independent second profile
derivative bound, from the proved second score and true posterior moments. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorProfileGradientSecondVariationBound (n : ℕ) (β t : ℝ) : ℝ :=
  Real.sqrt (n:ℝ)*(18*((n:ℝ)*((1-t)*β^2)/2)^2+
    (4*((n:ℝ)*((1-t)*β^2)/2)+vectorProfileSecondReactionBound n β t)+
      8*(n:ℝ)*vectorProfilePosteriorPowerMomentBound n β t 2)

theorem vectorProfileGradientSecondVariationBound_nonneg (n : ℕ) (β t : ℝ) (ht : t≤1) :
    0≤vectorProfileGradientSecondVariationBound n β t := by
  unfold vectorProfileGradientSecondVariationBound
  exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg
    (add_nonneg (by positivity) (add_nonneg (by positivity)
      (vectorProfileSecondReactionBound_nonneg n β t ht)))
    (mul_nonneg (by positivity) (vectorProfilePosteriorPowerMomentBound_nonneg n β t 2)))

theorem norm_vectorGridProfileTailRecursion_gradient_second_profile_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ‖deriv (deriv (fun φ=>gradient (vectorProfileTailRecursion
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t q φ p
          (vectorDyadicIndex j+3)) x)) θ‖≤vectorProfileGradientSecondVariationBound n β t := by
  let d:=vectorDyadicIndex j
  let s₀:=Paper.parisiGridRSBScheme μ d
  let s₁:=Paper.parisiGridRSBScheme ν d
  let C₀:=vectorClampedScheme s₀ q q.property
  let C₁:=vectorClampedScheme s₁ q q.property
  let Q:=4*((n:ℝ)*((1-t)*β^2)/2)+vectorProfileSecondReactionBound n β t
  let hθc : θ∈Icc (0:ℝ) 1:=⟨hθ.1.le,hθ.2.le⟩
  have hgrid : ∀i,i≤(d+1+1)+2→C₀.q i=C₁.q i:=fun _ _=>rfl
  have hQ : 0≤Q:=add_nonneg (by positivity)
    (vectorProfileSecondReactionBound_nonneg n β t ht.le)
  have hsecond : ∀φ∈Ioo (0:ℝ) 1,∀z : (Fin (d+3)→Field n)×Configuration n,
      |deriv (deriv (fun ψ=>vectorProfilePosteriorLogDensity C₀ C₁ β t p x (d+2) ψ z)) φ|≤Q :=
    fun φ hφ z=>abs_vectorGridProfileClampedPosteriorLogDensity_second_deriv_le
      μ ν j β t hβ ht q p x φ hφ z
  have hd:=norm_vectorProfileRecursion_gradient_second_profile_deriv_le_posterior_moment
    C₀ C₁ hgrid β t ht.le p x (d+2) (by omega) Q hQ hsecond θ hθ
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
  have hm:=(vectorClampedGridPosterior_fieldEnvelope_pow_moment
    (n:=n) (Paper.parisiMix μ ν θ) j β t hβ ht q p x 2).2
  have hb : Real.sqrt (n:ℝ)*(18*((n:ℝ)*((1-t)*β^2)/2)^2+Q+8*(n:ℝ)*
      (∫z,(vectorProfilePosteriorFieldEnvelope
        (vectorClampedScheme (Paper.parisiGridRSBScheme (Paper.parisiMix μ ν θ) d) q q.property)
          β t p x (d+2) z.1)^2∂vectorTailGaussianPosterior
        (vectorClampedScheme (Paper.parisiGridRSBScheme (Paper.parisiMix μ ν θ) d) q q.property)
          β t p x (d+3)))≤vectorProfileGradientSecondVariationBound n β t := by
    unfold vectorProfileGradientSecondVariationBound
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hm (by positivity))) (Real.sqrt_nonneg _)
  have he : (fun φ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q φ p (d+3)) x)=
      (fun φ=>gradient (vectorProfileRecursion C₀ C₁ β t φ p (d+3)) x) := by
    funext φ
    rw [vectorProfileTailRecursion_eq_clampedProfile s₀ s₁ β t q φ q.property p (by omega)]
  change ‖deriv (deriv (fun φ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q φ p (d+3)) x)) θ‖≤_
  rw [he]
  exact hd.trans hb

end QuantitativePaper
