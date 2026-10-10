module
public import QuantitativeFollowup.ConcentratingPairing
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Actual local-density and signal pairings for the concentrating
quartic. All boundary atoms are retained: the quartic vanishes at both
endpoints, so restriction to the open interval is an exact identity. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem concentrating_weighted_integrable (D : ℝ → ℝ) (hD : Continuous D)
    (a ell : ℝ) (hell : 0 < ell) :
    Integrable (fun x => D x*concentratingIntervalBump a ell x) volume :=
  (hD.mul (contDiff_concentratingIntervalBump a ell).continuous).integrable_of_hasCompactSupport
    ((concentratingIntervalBump_hasCompactSupport a ell hell).mul_left)

theorem concentrating_weighted_square_integrable (D : ℝ → ℝ) (hD : Continuous D)
    (a ell : ℝ) (hell : 0 < ell) :
    Integrable (fun x => D x*(concentratingIntervalBump a ell x)^2) volume :=
  (hD.mul ((contDiff_concentratingIntervalBump a ell).continuous.pow 2)).integrable_of_hasCompactSupport
    (by
      apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc a (a+ell)))
      intro x hx
      by_contra hn
      apply hx
      change D x*(concentratingIntervalBump a ell x)^2=0
      rw [concentratingIntervalBump_zero_outside a ell x hell (fun hi => hn ⟨hi.1.le,hi.2.le⟩)]
      simp)

theorem concentrating_weighted_integral_eq (D : ℝ → ℝ)
    (a ell : ℝ) (hell : 0 < ell) :
    (∫x : ℝ, D x*concentratingIntervalBump a ell x) = concentratingDelta a ell D := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hxi : x ∈ Ioo a (a+ell) := by
    by_contra hn
    apply hx
    change D x*concentratingIntervalBump a ell x=0
    rw [concentratingIntervalBump_zero_outside a ell x hell hn,mul_zero]
  exact ⟨hxi.1,hxi.2.le⟩

theorem concentrating_density_square_bound (D : ℝ → ℝ) (hD : Continuous D)
    (hDn : ∀x, 0 ≤ D x) (a ell : ℝ) (hell : 0 < ell)
    (eta : Measure ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hdensity : eta.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal d • volume.restrict (Ioo a (a+ell))) :
    (∫x : ℝ, D x*(concentratingIntervalBump a ell x)^2 ∂eta) ≤
      d*concentratingDelta a ell D := by
  have hi := concentrating_weighted_square_integrable D hD a ell hell
  have hnonneg : ∀x, 0 ≤ D x*(concentratingIntervalBump a ell x)^2 :=
    fun x => mul_nonneg (hDn x) (sq_nonneg _)
  have heq (mu : Measure ℝ) :
      (∫x in Ioo a (a+ell), D x*(concentratingIntervalBump a ell x)^2 ∂mu) =
        ∫x : ℝ, D x*(concentratingIntervalBump a ell x)^2 ∂mu := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [concentratingIntervalBump_zero_outside a ell x hell hx]
    simp
  rw [←heq eta]
  calc
    _ ≤ ∫x : ℝ, D x*(concentratingIntervalBump a ell x)^2
        ∂(ENNReal.ofReal d • volume.restrict (Ioo a (a+ell))) :=
      integral_mono_measure hdensity (.of_forall hnonneg)
        ((hi.mono_measure Measure.restrict_le_self).smul_measure ENNReal.ofReal_ne_top)
    _ = d*(∫x : ℝ, D x*(concentratingIntervalBump a ell x)^2) := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hd,heq volume]
      rfl
    _ ≤ d*(∫x : ℝ, D x*concentratingIntervalBump a ell x) := by
      apply mul_le_mul_of_nonneg_left _ hd
      apply integral_mono hi (concentrating_weighted_integrable D hD a ell hell)
      intro x
      have hp := concentratingIntervalBump_bounds a ell x
      exact mul_le_mul_of_nonneg_left (by nlinarith :
        (concentratingIntervalBump a ell x)^2 ≤ concentratingIntervalBump a ell x) (hDn x)
    _ = _ := by rw [concentrating_weighted_integral_eq D a ell hell]

theorem concentrating_signal_lower (D psi : ℝ → ℝ) (hD : Continuous D)
    (hDn : ∀x, 0 ≤ D x) (hpsi : Measurable psi) (K : ℝ)
    (hK : ∀x, ‖psi x‖ ≤ K) (a ell A : ℝ) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a+ell ≤ 1)
    (hsignal : ∀x∈Ioo a (a+ell), A ≤ psi x) :
    A*concentratingDelta a ell D ≤
      ∫x in (0 : ℝ)..1, psi x*D x*concentratingIntervalBump a ell x := by
  have hi := concentrating_weighted_integrable D hD a ell hell
  have hip := hi.bdd_mul hpsi.aestronglyMeasurable (.of_forall hK)
  have hs : Function.support (fun x=>psi x*(D x*concentratingIntervalBump a ell x)) ⊆
      Ioc (0 : ℝ) 1 := by
    intro x hx
    have hxi : x∈Ioo a (a+ell) := by
      by_contra hn
      apply hx
      change psi x*(D x*concentratingIntervalBump a ell x)=0
      rw [concentratingIntervalBump_zero_outside a ell x hell hn,mul_zero,mul_zero]
    exact ⟨ha.trans_lt hxi.1,hxi.2.le.trans he⟩
  have hsignal' : ∀x, A*(D x*concentratingIntervalBump a ell x) ≤
      psi x*(D x*concentratingIntervalBump a ell x) := by
    intro x
    by_cases hx : x∈Ioo a (a+ell)
    · exact mul_le_mul_of_nonneg_right (hsignal x hx)
        (mul_nonneg (hDn x) (concentratingIntervalBump_bounds a ell x).1)
    · rw [concentratingIntervalBump_zero_outside a ell x hell hx]
      simp
  have hh := integral_mono (hi.const_mul A) hip hsignal'
  rw [integral_const_mul,concentrating_weighted_integral_eq D a ell hell,
    ←intervalIntegral.integral_eq_integral_of_support_subset hs] at hh
  convert hh using 1
  apply intervalIntegral.integral_congr
  intro x _
  ring

end QuantitativeFollowup
