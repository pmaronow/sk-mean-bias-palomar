module
public import QuantitativeFollowup.ConcentratingIntervalRegularity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! Genuine integration-by-parts and curvature-mass bounds for the
concentrating test. The input is an actual differentiable response S,
with derivative D, rather than a supplied pairing conclusion. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def concentratingDelta (a ell : ℝ) (D : ℝ → ℝ) : ℝ :=
  ∫x in a..a+ell, D x * concentratingIntervalBump a ell x

theorem concentrating_pairing (S D : ℝ → ℝ) (hS : Continuous S) (hD : Continuous D)
    (a ell : ℝ) (hell : 0 < ell)
    (hd : ∀ x ∈ Icc a (a+ell), HasDerivAt S (D x) x) :
    (∫x in a..a+ell, concentratingIntervalIncrement a ell x * (S x-x)) =
      8*ell/15 - concentratingDelta a ell D := by
  have hc := (contDiff_concentratingIntervalBump a ell).continuous
  have hchi := (lipschitz_concentratingIntervalIncrement a ell hell).continuous
  have hDu : Continuous (fun x => D x-1) := hD.sub continuous_const
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x => S x-x) (v := concentratingIntervalBump a ell)
    (u' := fun x => D x-1) (v' := concentratingIntervalIncrement a ell)
    (a := a) (b := a+ell) ((hS.sub continuous_id).continuousOn) hc.continuousOn
    (fun x hx => by
      rw [min_eq_left (by linarith : a ≤ a+ell), max_eq_right (by linarith : a ≤ a+ell)] at hx
      exact (hd x ⟨hx.1.le,hx.2.le⟩).sub (hasDerivAt_id x))
    (fun x _ => hasDerivAt_concentratingIntervalBump a ell x)
    (hDu.intervalIntegrable a (a+ell)) (hchi.intervalIntegrable a (a+ell))
  have hza := concentratingIntervalBump_zero_outside a ell a hell (by simp)
  have hzb := concentratingIntervalBump_zero_outside a ell (a+ell) hell (by simp)
  have hiD : IntervalIntegrable (fun x => D x*concentratingIntervalBump a ell x) volume a (a+ell) :=
    (hD.mul hc).intervalIntegrable a (a+ell)
  have heq : (fun x => (D x-1)*concentratingIntervalBump a ell x) =
      (fun x => D x*concentratingIntervalBump a ell x-concentratingIntervalBump a ell x) := by
    funext x
    ring
  calc
    _ = ∫x in a..a+ell, (S x-x)*concentratingIntervalIncrement a ell x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = -(∫x in a..a+ell, (D x-1)*concentratingIntervalBump a ell x) := by
      rw [hip, hza, hzb, mul_zero, mul_zero, sub_zero, zero_sub]
    _ = 8*ell/15-concentratingDelta a ell D := by
      rw [heq, intervalIntegral.integral_sub hiD (hc.intervalIntegrable a (a+ell)),
        concentratingIntervalBump_interval_integral a ell hell, concentratingDelta]
      ring

theorem concentratingDelta_nonneg_le_increment (S D : ℝ → ℝ)
    (hD : Continuous D) (hDn : ∀x, 0 ≤ D x) (a ell : ℝ) (hell : 0 < ell)
    (hd : ∀ x ∈ Icc a (a+ell), HasDerivAt S (D x) x) :
    0 ≤ concentratingDelta a ell D ∧ concentratingDelta a ell D ≤ S (a+ell)-S a := by
  have hc := (contDiff_concentratingIntervalBump a ell).continuous
  refine ⟨intervalIntegral.integral_nonneg_of_forall (by linarith) (fun x =>
    mul_nonneg (hDn x) (concentratingIntervalBump_bounds a ell x).1), ?_⟩
  have hi : (∫x in a..a+ell, D x) = S (a+ell)-S a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hD.intervalIntegrable a (a+ell))
    intro x hx
    rw [uIcc_of_le (by linarith : a ≤ a+ell)] at hx
    exact hd x hx
  rw [←hi]
  apply intervalIntegral.integral_mono_on (by linarith) ((hD.mul hc).intervalIntegrable a (a+ell)) (hD.intervalIntegrable a (a+ell))
  intro x _
  calc
    _ ≤ D x*1 := mul_le_mul_of_nonneg_left (concentratingIntervalBump_bounds a ell x).2 (hDn x)
    _ = D x := mul_one _

theorem concentrating_pairing_unit (S D : ℝ → ℝ) (hS : Continuous S) (hD : Continuous D)
    (a ell : ℝ) (ha : 0 ≤ a) (he : a+ell ≤ 1) (hell : 0 < ell)
    (hd : ∀ x ∈ Icc a (a+ell), HasDerivAt S (D x) x) :
    (∫x in (0 : ℝ)..1, concentratingIntervalIncrement a ell x * (S x-x)) =
      8*ell/15 - concentratingDelta a ell D := by
  let f := fun x => concentratingIntervalIncrement a ell x * (S x-x)
  have hs : Function.support f ⊆ Ioc a (a+ell) := by
    intro x hx
    have hx' : x ∈ Ioo a (a+ell) := by
      by_contra hn
      apply hx
      dsimp only [f]
      rw [concentratingIntervalIncrement_zero_outside a ell x hell hn, zero_mul]
    exact ⟨hx'.1,hx'.2.le⟩
  have hu : Function.support f ⊆ Ioc (0 : ℝ) 1 :=
    fun x hx => ⟨ha.trans_lt (hs hx).1, (hs hx).2.trans he⟩
  change (∫x in (0 : ℝ)..1,f x) = _
  rw [intervalIntegral.integral_eq_integral_of_support_subset hu,
    ←intervalIntegral.integral_eq_integral_of_support_subset hs]
  exact concentrating_pairing S D hS hD a ell hell hd

end QuantitativeFollowup
