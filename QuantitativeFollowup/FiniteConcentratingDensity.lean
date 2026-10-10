module
public import QuantitativeFollowup.FiniteConcentratingPairing

@[expose] public section

/-! Atom-safe density comparison for finite smooth tests vanishing
outside the set on which domination holds. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup

theorem finiteConcentrating_density_square_bound_on (S : Finset ℕ) (a : ℕ→ℝ)
    (ell : ℝ) (hell : 0<ell) (ha : ∀i∈S,0≤a i) (he : ∀i∈S,a i+ell≤1)
    (hdisj : (S:Set ℕ).PairwiseDisjoint (fun i=>Ioo (a i) (a i+ell)))
    (D : ℝ→ℝ) (hD : Continuous D) (hDn : ∀x,0≤D x)
    (eta : Measure ℝ) (E : Set ℝ) (d : ℝ) (hd : 0≤d)
    (hdensity : eta.restrict E≤ENNReal.ofReal d • volume)
    (hzero : ∀x∉E,finiteConcentratingBump S a ell x=0) :
    (∫x : ℝ,D x*(finiteConcentratingBump S a ell x)^2 ∂eta) ≤
      d*(∫x in (0 : ℝ)..1,D x*finiteConcentratingBump S a ell x) := by
  have hi := finiteConcentrating_weighted_square_integrable S a ell hell ha he D hD
  have hn : ∀x,0≤D x*(finiteConcentratingBump S a ell x)^2 := fun x=>mul_nonneg (hDn x) (sq_nonneg _)
  have heq : (∫x in E,D x*(finiteConcentratingBump S a ell x)^2 ∂eta) =
      ∫x : ℝ,D x*(finiteConcentratingBump S a ell x)^2 ∂eta := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hzero x hx]
    simp
  rw [←heq]
  have hc := integral_mono_measure hdensity (.of_forall hn) (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal hd,smul_eq_mul] at hc
  have hs : (∫x : ℝ,D x*(finiteConcentratingBump S a ell x)^2) ≤
      ∫x : ℝ,D x*finiteConcentratingBump S a ell x := by
    apply integral_mono hi (finiteConcentrating_weighted_integrable S a ell hell ha he D hD)
    intro x
    have hp0 := finiteConcentratingBump_nonneg S a ell x
    have hp1 := finiteConcentratingBump_le_one S a ell hell hdisj x
    exact mul_le_mul_of_nonneg_left (by nlinarith : (finiteConcentratingBump S a ell x)^2≤
      finiteConcentratingBump S a ell x) (hDn x)
  have hu : (∫x in (0 : ℝ)..1,D x*finiteConcentratingBump S a ell x)=
      ∫x : ℝ,D x*finiteConcentratingBump S a ell x := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    by_contra hnot
    apply hx
    change D x*finiteConcentratingBump S a ell x=0
    rw [finiteConcentratingBump_zero_outside_unit S a ell hell ha he x hnot,mul_zero]
  rw [hu]
  exact hc.trans (mul_le_mul_of_nonneg_left hs hd)

end QuantitativeFollowup
