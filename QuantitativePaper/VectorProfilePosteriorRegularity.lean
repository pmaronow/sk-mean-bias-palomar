module
public import QuantitativePaper.VectorProfilePosteriorScore
public import QuantitativePaper.FieldSliceJetContinuity

@[expose] public section

/-! Actual joint profile/noise regularity of the posterior and its first
score. Gaussian coordinates stay fixed as the profile masses vary. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiff_vectorProfilePosteriorPotential_theta_noise (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ)
    (i : Option (Fin N)) :
    ContDiff ℝ ∞ (fun w : ℝ×(Fin (N+1)→Field n) =>
      vectorProfilePosteriorPotential s₀ s₁ β t p x N w.2 w.1 i) := by
  cases i with
  | none =>
    exact (contDiff_vectorProfileJointFunction_all_theta (n:=n) s₀ s₁ β t (N+1)).comp
      (contDiff_fst.prodMk (contDiff_const (c:=(p,x))))
  | some i =>
    have hh : ContDiff ℝ ∞ (fun z : Fin (N+1)→Field n=>
        (historyExtended (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z) (i+1)).2) :=
      contDiff_snd.comp ((contDiff_apply ℝ (VectorState n) _).comp
        ((contDiff_vectorHistoryFrom_initial_noise s₀ β t _ p (N+1)).comp
          (contDiff_const.prodMk contDiff_id)))
    exact (contDiff_vectorProfileJointFunction_all_theta (n:=n) s₀ s₁ β t (N+1-(i+1))).comp
      (contDiff_fst.prodMk (contDiff_const.prodMk (hh.comp contDiff_snd)))

theorem contDiff_vectorProfilePosteriorLogDensity_theta_noise (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (σ : Configuration n) :
    ContDiff ℝ ∞ (fun w : ℝ×(Fin (N+1)→Field n) =>
      vectorProfilePosteriorLogDensity s₀ s₁ β t p x N w.1 (w.2,σ)) := by
  have hT : ContDiff ℝ ∞ (fun w : ℝ×(Fin (N+1)→Field n) =>
      vectorTerminalExponent n β t p
        (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) w.2 (Fin.last (N+1))).2 σ) := by
    have hh : ContDiff ℝ ∞ (fun w : ℝ×(Fin (N+1)→Field n)=>
        (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) w.2 (Fin.last (N+1))).2) :=
      contDiff_snd.comp ((contDiff_apply ℝ (VectorState n) (Fin.last (N+1))).comp
      (((contDiff_vectorHistoryFrom_initial_noise s₀ β t _ p (N+1)).comp
        (contDiff_const.prodMk contDiff_id)).comp contDiff_snd))
    have he : ContDiff ℝ ∞ (fun y : Field n=>vectorTerminalExponent n β t p y σ) := by
      unfold vectorTerminalExponent fieldDot
      fun_prop
    exact he.comp hh
  refine hT.sub (ContDiff.sum fun i _=>?_)
  have hw : ContDiff ℝ ∞ (fun w : ℝ×(Fin (N+1)→Field n)=>
      vectorProfilePosteriorWeight s₀ s₁ N w.1 i) := by
    unfold vectorProfilePosteriorWeight
    fun_prop
  exact hw.mul (contDiff_vectorProfilePosteriorPotential_theta_noise s₀ s₁ β t p x N i)

theorem continuous_scalarParameter_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ×E→ℝ) (hf : ContDiff ℝ ∞ f) :
    Continuous (fun w : ℝ×E=>deriv (fun θ=>f (θ,w.2)) w.1) := by
  have he : (fun w : ℝ×E=>deriv (fun θ=>f (θ,w.2)) w.1)=
      fun w=>fderiv ℝ f w (1,0) := by
    funext w
    have hd := ((hf.differentiable (by simp) w).hasFDerivAt).comp_hasDerivAt w.1
      ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))
    exact hd.deriv
  rw [he]
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem measurable_vectorProfilePosteriorLogDensity (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) :
    Measurable (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact ((contDiff_vectorProfilePosteriorLogDensity_theta_noise s₀ s₁ β t p x N σ).comp
    (contDiff_const.prodMk contDiff_id)).continuous.measurable

theorem measurable_vectorProfilePosteriorLogDensity_deriv (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) :
    Measurable (fun z : (Fin (N+1)→Field n)×Configuration n=>
      deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact ((continuous_scalarParameter_deriv _
    (contDiff_vectorProfilePosteriorLogDensity_theta_noise s₀ s₁ β t p x N σ)).comp
      (continuous_const.prodMk continuous_id)).measurable

end QuantitativePaper
