module
public import QuantitativeFollowup.ConcentratingIntervalRegularity
public import QuantitativeFollowup.StieltjesLipschitz
public import Mathlib.Order.Monotone.Union

@[expose] public section

/-! The concentrating move is a genuine monotone, right-continuous
Stieltjes primitive. Admissibility is derived from the original local
measure lower bound and the checked Lipschitz constant of the bump. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def concentratingMovedProfile (f : ℝ → ℝ) (a ell tau x : ℝ) : ℝ :=
  f x - tau * concentratingIntervalIncrement a ell x

theorem stieltjes_increment_lower_of_density (f : StieltjesFunction ℝ)
    (a ell kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      f.measure.restrict (Ioo a (a+ell)))
    (x y : ℝ) (hx : x ∈ Icc a (a+ell)) (hy : y ∈ Icc a (a+ell)) (hxy : x ≤ y) :
    kappa * (y-x) ≤ f y-f x := by
  have hsub : Ioo x y ⊆ Ioo a (a+ell) :=
    fun z hz => ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
  have hd := hdensity (Ioo x y)
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo,
    Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hsub, Real.volume_Ioo] at hd
  have hm := measure_mono (Ioo_subset_Ioc_self : Ioo x y ⊆ Ioc x y) (μ := f.measure)
  rw [StieltjesFunction.measure_Ioc] at hm
  have hreal := hd.trans hm
  rw [smul_eq_mul, ←ENNReal.ofReal_mul hkappa] at hreal
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr (f.mono hxy))).mp hreal

theorem monotone_concentratingMovedProfile (f : StieltjesFunction ℝ)
    (a ell kappa tau : ℝ) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      f.measure.restrict (Ioo a (a+ell))) :
    Monotone (concentratingMovedProfile f a ell tau) := by
  have ht : tau * (32/ell^2) ≤ kappa := by
    have h : tau*32 ≤ kappa*ell^2 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mp htau.2
    have hp : 0 < ell^2 := sq_pos_of_pos hell
    have hd : (tau*32)/ell^2 ≤ kappa := (div_le_iff₀ hp).mpr h
    convert hd using 1
    ring
  have hmid : MonotoneOn (concentratingMovedProfile f a ell tau) (Icc a (a+ell)) := by
    intro x hx y hy hxy
    have hf := stieltjes_increment_lower_of_density f a ell kappa hkappa hdensity x y hx hy hxy
    have hc := (lipschitz_concentratingIntervalIncrement a ell hell).dist_le_mul y x
    change |concentratingIntervalIncrement a ell y - concentratingIntervalIncrement a ell x| ≤
      (32/ell^2)*|y-x| at hc
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hc
    have hs : concentratingIntervalIncrement a ell y - concentratingIntervalIncrement a ell x ≤
      (32/ell^2)*(y-x) := (le_abs_self _).trans hc
    have ht1 := mul_le_mul_of_nonneg_left hs htau.1
    have ht2 := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hxy)
    dsimp only [concentratingMovedProfile]
    nlinarith
  have hleft : MonotoneOn (concentratingMovedProfile f a ell tau) (Iic a) := by
    intro x hx y hy hxy
    have hx0 := concentratingIntervalIncrement_zero_outside a ell x hell
      (fun h => not_lt_of_ge hx h.1)
    have hy0 := concentratingIntervalIncrement_zero_outside a ell y hell
      (fun h => not_lt_of_ge hy h.1)
    simp only [concentratingMovedProfile, hx0, hy0, mul_zero, sub_zero]
    exact f.mono hxy
  have hright : MonotoneOn (concentratingMovedProfile f a ell tau) (Ici (a+ell)) := by
    intro x hx y hy hxy
    have hx0 := concentratingIntervalIncrement_zero_outside a ell x hell
      (fun h => not_lt_of_ge hx h.2)
    have hy0 := concentratingIntervalIncrement_zero_outside a ell y hell
      (fun h => not_lt_of_ge hy h.2)
    simp only [concentratingMovedProfile, hx0, hy0, mul_zero, sub_zero]
    exact f.mono hxy
  have hu : Icc a (a+ell) ∪ Ici (a+ell) = Ici a := by
    ext x
    constructor
    · intro hx
      rcases hx with hx|hx
      · exact hx.1
      · exact (by linarith : a ≤ a+ell).trans hx
    · intro hx
      by_cases hy : x ≤ a+ell
      · exact Or.inl ⟨hx,hy⟩
      · exact Or.inr (le_of_not_ge hy)
  have hrest := hmid.union_right hright (isGreatest_Icc (by linarith)) isLeast_Ici
  rw [hu] at hrest
  exact hleft.Iic_union_Ici hrest

def concentratingMovedStieltjes (f : StieltjesFunction ℝ) (a ell kappa tau : ℝ)
    (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      f.measure.restrict (Ioo a (a+ell))) : StieltjesFunction ℝ where
  toFun := concentratingMovedProfile f a ell tau
  mono' := monotone_concentratingMovedProfile f a ell kappa tau hell hkappa htau hdensity
  right_continuous' x := (f.right_continuous x).sub
    (((lipschitz_concentratingIntervalIncrement a ell hell).continuous.continuousAt).const_mul tau).continuousWithinAt

@[simp] theorem concentratingMovedStieltjes_apply (f : StieltjesFunction ℝ)
    (a ell kappa tau : ℝ) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      f.measure.restrict (Ioo a (a+ell))) (x : ℝ) :
    concentratingMovedStieltjes f a ell kappa tau hell hkappa htau hdensity x =
      f x - tau * concentratingIntervalIncrement a ell x := rfl

theorem concentratingMovedStieltjes_eq_outside (f : StieltjesFunction ℝ)
    (a ell kappa tau : ℝ) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      f.measure.restrict (Ioo a (a+ell))) (x : ℝ) (hx : x ∉ Ioo a (a+ell)) :
    concentratingMovedStieltjes f a ell kappa tau hell hkappa htau hdensity x = f x := by
  rw [concentratingMovedStieltjes_apply, concentratingIntervalIncrement_zero_outside a ell x hell hx,
    mul_zero, sub_zero]

end QuantitativeFollowup
