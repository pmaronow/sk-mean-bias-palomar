module
public import QuantitativeFollowup.ConcentratingIntervalRegularity
public import QuantitativePaper.ResponseC1Test

@[expose] public section

/-! The actual concentrating quartic is a genuine global C¹ response
 test. Its endpoints and derivative are supplied by the proved quartic
 calculus, rather than by a regularity predicate assumed for the test. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
namespace QuantitativeFollowup

def concentratingResponseTest (a ell : ℝ) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a+ell ≤ 1) : ResponseC1Test where
  value := concentratingIntervalBump a ell
  slope := concentratingIntervalIncrement a ell
  continuous := (contDiff_concentratingIntervalBump a ell).continuous
  continuous_slope := (lipschitz_concentratingIntervalIncrement a ell hell).continuous
  hasDerivAt := hasDerivAt_concentratingIntervalBump a ell
  zero_left := concentratingIntervalBump_zero_outside a ell 0 hell
    (fun hx => not_lt_of_ge ha hx.1)
  zero_right := concentratingIntervalBump_zero_outside a ell 1 hell
    (fun hx => not_lt_of_ge he hx.2)

@[simp] theorem concentratingResponseTest_value (a ell : ℝ) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a+ell ≤ 1) :
    (concentratingResponseTest a ell hell ha he).value = concentratingIntervalBump a ell := rfl

@[simp] theorem concentratingResponseTest_slope (a ell : ℝ) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a+ell ≤ 1) :
    (concentratingResponseTest a ell hell ha he).slope = concentratingIntervalIncrement a ell := rfl

theorem concentratingResponseTest_energy (a ell : ℝ) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a+ell ≤ 1) :
    (∫x in (0 : ℝ)..1, ((concentratingResponseTest a ell hell ha he).slope x)^2) =
      512/(105*ell) := by
  simpa only [concentratingResponseTest_slope, ←deriv_concentratingIntervalBump] using
    concentratingIntervalBump_unit_energy a ell hell ha he

end QuantitativeFollowup
