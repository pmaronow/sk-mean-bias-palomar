module
public import QuantitativePaper.VectorGridProfileClampedSecondVariation

@[expose] public section

/-! The genuine clamped-grid posterior second score is bounded by actual
model constants. Every node bound is derived from the restarted telescope. -/
noncomputable section
open Set
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem abs_vectorGridProfileClampedPosteriorLogDensity_second_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1)
    (z : (Fin (vectorDyadicIndex j+3)→Field n)×Configuration n) :
    let C₀:=vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property
    let C₁:=vectorClampedScheme (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) q q.property
    |deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity C₀ C₁ β t p x
      (vectorDyadicIndex j+2) φ z)) θ|≤
      4*((n:ℝ)*((1-t)*β^2)/2)+vectorProfileSecondReactionBound n β t := by
  let d:=vectorDyadicIndex j
  let C₀:=vectorClampedScheme (Paper.parisiGridRSBScheme μ d) q q.property
  let C₁:=vectorClampedScheme (Paper.parisiGridRSBScheme ν d) q q.property
  apply vectorProfilePosteriorLogDensity_second_deriv_bound_of_potential_bound C₀ C₁
    (fun _ _=>rfl) β t θ ht.le hθ p x (d+2) (by omega) z
    (vectorProfileSecondReactionBound n β t) (vectorProfileSecondReactionBound_nonneg n β t ht.le)
  intro i
  cases i with
  | none =>
    exact (norm_vectorGridProfileClampedRecursion_second_profile_deriv_le μ ν j β t hβ ht q p x
      (d+2+1) (by omega) θ hθ)
  | some i =>
    exact (norm_vectorGridProfileClampedRecursion_second_profile_deriv_le μ ν j β t hβ ht q p _
      (d+2+1-(i+1)) (by omega) θ hθ)

end QuantitativePaper
