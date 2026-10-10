module
public import QuantitativeFollowup.ConcentratingBumpSharp
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-! Actual scaled concentrating tests on an arbitrary positive-length
interval, with compact support and the literal mass/energy constants. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def concentratingIntervalBump (a ell x : ℝ) : ℝ := concentratingBump ((x-a)/ell)
def concentratingIntervalIncrement (a ell x : ℝ) : ℝ := concentratingBumpDerivative ((x-a)/ell)/ell

theorem contDiff_concentratingIntervalBump (a ell : ℝ) :
    ContDiff ℝ 1 (concentratingIntervalBump a ell) :=
  contDiff_concentratingBump.comp (by fun_prop : ContDiff ℝ 1 (fun x : ℝ => (x-a)/ell))

theorem hasDerivAt_concentratingIntervalBump (a ell x : ℝ) :
    HasDerivAt (concentratingIntervalBump a ell) (concentratingIntervalIncrement a ell x) x := by
  have hd := (hasDerivAt_concentratingBump ((x-a)/ell)).comp x
    (((hasDerivAt_id x).sub_const a).div_const ell)
  convert hd using 1
  · funext z
    dsimp only [concentratingIntervalBump,Function.comp_def,id_eq]
  · dsimp only [concentratingIntervalIncrement]
    ring

theorem deriv_concentratingIntervalBump (a ell : ℝ) :
    deriv (concentratingIntervalBump a ell)=concentratingIntervalIncrement a ell :=
  funext fun x => (hasDerivAt_concentratingIntervalBump a ell x).deriv

theorem concentratingIntervalBump_bounds (a ell x : ℝ) :
    0≤concentratingIntervalBump a ell x ∧ concentratingIntervalBump a ell x≤1 :=
  concentratingBump_nonneg_le_one _

theorem concentratingIntervalBump_zero_outside (a ell x : ℝ) (hell : 0<ell)
    (hx : x∉Ioo a (a+ell)) : concentratingIntervalBump a ell x=0 := by
  apply concentratingBump_zero_outside
  intro hy
  have hright := (div_lt_iff₀ hell).mp hy.2
  have hxleft : a<x := by
    have hp : 0<x-a := (div_pos_iff_of_pos_right hell).mp hy.1
    linarith
  exact hx ⟨hxleft,by linarith⟩

theorem concentratingIntervalIncrement_zero_outside (a ell x : ℝ) (hell : 0<ell)
    (hx : x∉Ioo a (a+ell)) : concentratingIntervalIncrement a ell x=0 := by
  have hy : (x-a)/ell∉Ioo (0 : ℝ) 1 := by
    intro hy
    have hxleft : a<x := by
      have hp : 0<x-a := (div_pos_iff_of_pos_right hell).mp hy.1
      linarith
    have hright := (div_lt_iff₀ hell).mp hy.2
    exact hx ⟨hxleft,by linarith⟩
  rw [concentratingIntervalIncrement,concentratingBumpDerivative_zero_outside _ hy,zero_div]

theorem concentratingIntervalIncrement_bound (a ell x : ℝ) (hell : 0<ell) :
    |concentratingIntervalIncrement a ell x|≤4/ell := by
  rw [concentratingIntervalIncrement,abs_div,abs_of_pos hell]
  exact div_le_div_of_nonneg_right (concentratingBumpDerivative_bound _) hell.le

theorem concentratingIntervalBump_hasCompactSupport (a ell : ℝ) (hell : 0<ell) :
    HasCompactSupport (concentratingIntervalBump a ell) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc a (a+ell)))
  intro x hx
  by_contra hn
  exact hx (concentratingIntervalBump_zero_outside a ell x hell (fun hh => hn ⟨hh.1.le,hh.2.le⟩))

theorem concentratingIntervalBump_interval_integral (a ell : ℝ) (hell : 0<ell) :
    (∫x in a..a+ell,concentratingIntervalBump a ell x)=8*ell/15 := by
  change (∫x in a..a+ell,(fun y => concentratingBump (y/ell)) (x-a))=8*ell/15
  rw [intervalIntegral.integral_comp_sub_right (fun y => concentratingBump (y/ell)) a]
  simp only [sub_self,add_sub_cancel_left]
  rw [intervalIntegral.integral_comp_div concentratingBump hell.ne']
  simp only [zero_div,div_self hell.ne',smul_eq_mul,concentratingBump_integral]
  ring

theorem concentratingIntervalBump_unit_integral (a ell : ℝ) (hell : 0<ell)
    (ha : 0≤a) (he : a+ell≤1) :
    (∫x in (0 : ℝ)..1,concentratingIntervalBump a ell x)=8*ell/15 := by
  have hs : Function.support (concentratingIntervalBump a ell)⊆Ioc a (a+ell) := by
    intro x hx
    have hxi : x∈Ioo a (a+ell) := by
      by_contra hh
      exact hx (concentratingIntervalBump_zero_outside a ell x hell hh)
    exact ⟨hxi.1,hxi.2.le⟩
  have hu : Function.support (concentratingIntervalBump a ell)⊆Ioc (0 : ℝ) 1 :=
    fun x hx => ⟨ha.trans_lt (hs hx).1,(hs hx).2.trans he⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hu,
    ←intervalIntegral.integral_eq_integral_of_support_subset hs]
  exact concentratingIntervalBump_interval_integral a ell hell

theorem concentratingIntervalBump_interval_energy (a ell : ℝ) (hell : 0<ell) :
    (∫x in a..a+ell,(deriv (concentratingIntervalBump a ell) x)^2)=512/(105*ell) := by
  rw [deriv_concentratingIntervalBump]
  have heq : (fun x => (concentratingIntervalIncrement a ell x)^2)=
      (fun x => (1/ell^2)*(concentratingBumpDerivative ((x-a)/ell))^2) := by
    funext x
    dsimp only [concentratingIntervalIncrement]
    ring
  rw [heq,intervalIntegral.integral_const_mul]
  have hc : (∫x in a..a+ell,(concentratingBumpDerivative ((x-a)/ell))^2)=ell*(512/105) := by
    change (∫x in a..a+ell,(fun y => (concentratingBumpDerivative (y/ell))^2) (x-a))=_
    rw [intervalIntegral.integral_comp_sub_right (fun y => (concentratingBumpDerivative (y/ell))^2) a]
    simp only [sub_self,add_sub_cancel_left]
    rw [intervalIntegral.integral_comp_div (fun y => (concentratingBumpDerivative y)^2) hell.ne']
    simp only [zero_div,div_self hell.ne',smul_eq_mul]
    rw [←deriv_concentratingBump,concentratingBump_energy]
  rw [hc]
  field_simp

theorem concentratingIntervalBump_unit_energy (a ell : ℝ) (hell : 0<ell)
    (ha : 0≤a) (he : a+ell≤1) :
    (∫x in (0 : ℝ)..1,(deriv (concentratingIntervalBump a ell) x)^2)=512/(105*ell) := by
  rw [deriv_concentratingIntervalBump]
  have hs : Function.support (fun x => (concentratingIntervalIncrement a ell x)^2)⊆Ioc a (a+ell) := by
    intro x hx
    have hxi : x∈Ioo a (a+ell) := by
      by_contra hh
      apply hx
      change (concentratingIntervalIncrement a ell x)^2=0
      rw [concentratingIntervalIncrement_zero_outside a ell x hell hh,zero_pow (by norm_num : (2 : ℕ)≠0)]
    exact ⟨hxi.1,hxi.2.le⟩
  have hu : Function.support (fun x => (concentratingIntervalIncrement a ell x)^2)⊆Ioc (0 : ℝ) 1 :=
    fun x hx => ⟨ha.trans_lt (hs hx).1,(hs hx).2.trans he⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hu,
    ←intervalIntegral.integral_eq_integral_of_support_subset hs,←deriv_concentratingIntervalBump]
  exact concentratingIntervalBump_interval_energy a ell hell

end QuantitativeFollowup
