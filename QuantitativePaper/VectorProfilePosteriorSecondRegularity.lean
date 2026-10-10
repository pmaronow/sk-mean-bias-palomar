module
public import QuantitativePaper.VectorProfilePosteriorSecondScore

@[expose] public section

/-! Genuine joint regularity and measurability of the second posterior
score, obtained by differentiating the actual globally smooth log density. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiff_scalarParameter_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ×E→ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun w : ℝ×E=>deriv (fun θ=>f (θ,w.2)) w.1) := by
  have he : (fun w : ℝ×E=>deriv (fun θ=>f (θ,w.2)) w.1)=
      fun w=>fderiv ℝ f w (1,0) := by
    funext w
    exact (((hf.differentiable (by simp) w).hasFDerivAt).comp_hasDerivAt w.1
      ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))).deriv
  rw [he]
  exact (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

theorem measurable_vectorProfilePosteriorLogDensity_second_deriv (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) :
    Measurable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact ((contDiff_scalarParameter_deriv _ (contDiff_scalarParameter_deriv _
    (contDiff_vectorProfilePosteriorLogDensity_theta_noise s₀ s₁ β t p x N σ))).continuous.comp
      (continuous_const.prodMk continuous_id)).measurable

end QuantitativePaper
