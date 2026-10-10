module
public import QuantitativeFollowup.ConcentratingIntervalBump

@[expose] public section

/-! Literal scaled C1,1 constants. The actual first derivative is globally
Lipschitz, so its actual second derivative is bounded even at the points where
Lean defines a derivative of a nondifferentiable function to be zero. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem lipschitz_concentratingIntervalIncrement (a ell : ℝ) (hell : 0 < ell) :
    LipschitzWith ⟨32 / ell ^ 2, by positivity⟩ (concentratingIntervalIncrement a ell) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hd := lipschitz_concentratingBumpDerivative.dist_le_mul ((x-a)/ell) ((y-a)/ell)
  simp only [Real.dist_eq, NNReal.coe_ofNat] at hd
  have he : |(x-a)/ell - (y-a)/ell| = |x-y|/ell := by
    rw [←sub_div, abs_div, abs_of_pos hell]
    have hz : (x-a)-(y-a)=x-y := by ring
    rw [hz]
  rw [he] at hd
  change |concentratingIntervalIncrement a ell x - concentratingIntervalIncrement a ell y| ≤
    (32 / ell ^ 2) * |x-y|
  rw [concentratingIntervalIncrement, concentratingIntervalIncrement, ←sub_div,
    abs_div, abs_of_pos hell]
  calc
    _ ≤ (32 * (|x-y|/ell))/ell := div_le_div_of_nonneg_right hd hell.le
    _ = (32 / ell ^ 2) * |x-y| := by simp only [div_eq_mul_inv]; ring

theorem concentratingIntervalIncrement_second_derivative_bound (a ell x : ℝ)
    (hell : 0 < ell) : |deriv (concentratingIntervalIncrement a ell) x| ≤ 32 / ell ^ 2 := by
  have hn := norm_deriv_le_of_lipschitz (x₀ := x)
    (lipschitz_concentratingIntervalIncrement a ell hell)
  change ‖deriv (concentratingIntervalIncrement a ell) x‖ ≤ 32 / ell ^ 2 at hn
  simpa only [Real.norm_eq_abs] using hn

theorem concentratingIntervalBump_second_derivative_bound_ae (a ell : ℝ)
    (hell : 0 < ell) :
    ∀ᵐx∂volume, |deriv (deriv (concentratingIntervalBump a ell)) x| ≤ 32 / ell ^ 2 := by
  rw [deriv_concentratingIntervalBump]
  exact Filter.Eventually.of_forall (fun x =>
    concentratingIntervalIncrement_second_derivative_bound a ell x hell)

theorem concentratingIntervalIncrement_hasCompactSupport (a ell : ℝ) (hell : 0 < ell) :
    HasCompactSupport (concentratingIntervalIncrement a ell) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc a (a+ell)))
  intro x hx
  by_contra hn
  exact hx (concentratingIntervalIncrement_zero_outside a ell x hell
    (fun hh => hn ⟨hh.1.le, hh.2.le⟩))

end QuantitativeFollowup
