module
public import Paper.ParisiWeightedVolterra
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Exponential absorption of the genuine square-root Volterra kernel.
The finite bound on the comparison function is used only to attain its
weighted maximum, and never enters the resulting constant. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 1500000

theorem uniform_scalar_volterra_absorption (f : ℝ → ℝ) (hf : Continuous f)
    (T A K ell : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hell : 0 < ell) (hk : K * (3 * Real.sqrt ell⁻¹) ≤ 1 / 2)
    (hnon : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ f t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T, f t ≤ A + K *
      (∫ s in t..T, f s * (Real.sqrt (s-t))⁻¹)) :
    ∀ t ∈ Icc (0 : ℝ) T, f t ≤ 2 * A * Real.exp (ell*T) := by
  let w : ℝ → ℝ := fun t => Real.exp (ell*t) * f t
  have hw : Continuous w := (show Continuous (fun t : ℝ => Real.exp (ell*t)) by
    fun_prop).mul hf
  obtain ⟨u,hu,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    hw.continuousOn
  let R := w u
  have hR : 0 ≤ R := mul_nonneg (Real.exp_pos _).le (hnon u hu)
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (hus : u ≤ s) :
      Real.exp (ell*u) * f s ≤ R * parisiDecayWeight ell u s := by
    have hh := hmax hs
    change Real.exp (ell*s) * f s ≤ R at hh
    have he : Real.exp (ell*u) = Real.exp (-ell*(s-u)) * Real.exp (ell*s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, mul_assoc]
    have hp := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-ell*(s-u))).le
    simpa only [parisiDecayWeight, max_eq_left (sub_nonneg.mpr hus), mul_comm] using hp
  have hiK := intervalIntegrable_bdd_mul_inv_sqrt_sub (parisiDecayWeight ell u)
    (show Measurable (parisiDecayWeight ell u) by unfold parisiDecayWeight; fun_prop)
    (parisiDecayWeight_nonneg ell u) (parisiDecayWeight_le_one ell hell.le u) u T hu.2
  have hfR (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : f s ≤ R := by
    have he0 : 1 ≤ Real.exp (ell*s) := Real.one_le_exp_iff.mpr (mul_nonneg hell.le hs.1)
    have hh : f s ≤ Real.exp (ell*s)*f s := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he0 (hnon s hs)
    exact hh.trans (hmax hs)
  have hiF : IntervalIntegrable (fun s => f s * (Real.sqrt (s-u))⁻¹) volume u T := by
    apply ((intervalIntegrable_inv_sqrt_sub u T hu.2).const_mul R).mono_fun'
    · exact (hf.measurable.mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      rw [uIoc_of_le hu.2] at hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hu.1.trans hs.1.le,hs.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnon s hsT) (by positivity))]
      exact mul_le_mul_of_nonneg_right (hfR s hsT) (by positivity)
  have hiW : IntervalIntegrable (fun s => Real.exp (ell*u)*
      (f s * (Real.sqrt (s-u))⁻¹)) volume u T := hiF.const_mul _
  have hInt := intervalIntegral.integral_mono_on hu.2 hiW (hiK.const_mul R)
    (fun s hs => by
      have hh := mul_le_mul_of_nonneg_right (hb s ⟨hu.1.trans hs.1,hs.2⟩ hs.1)
        (inv_nonneg.mpr (Real.sqrt_nonneg (s-u)))
      simpa only [mul_assoc] using hh)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hInt
  have hBound := integral_parisiDecayWeight_inv_sqrt_le ell hell u T hu.2
  have hInt' : Real.exp (ell*u) *
      (∫ s in u..T, f s * (Real.sqrt (s-u))⁻¹) ≤ R * (3 * Real.sqrt ell⁻¹) :=
    hInt.trans (mul_le_mul_of_nonneg_left hBound hR)
  have hineq' := mul_le_mul_of_nonneg_left (hineq u hu) (Real.exp_pos (ell*u)).le
  have heT : Real.exp (ell*u) ≤ Real.exp (ell*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hell.le)
  have hRA : R ≤ Real.exp (ell*T)*A+R/2 := by
    change R ≤ Real.exp (ell*u)*(A+K*_) at hineq'
    calc
      R ≤ Real.exp (ell*u)*A+K*(Real.exp (ell*u)*
          (∫ s in u..T,f s*(Real.sqrt (s-u))⁻¹)) := hineq'.trans_eq (by ring)
      _ ≤ Real.exp (ell*T)*A+K*(R*(3*Real.sqrt ell⁻¹)) :=
        add_le_add (mul_le_mul_of_nonneg_right heT hA)
          (mul_le_mul_of_nonneg_left hInt' hK)
      _ ≤ Real.exp (ell*T)*A+R/2 := by
        have hh := mul_le_mul_of_nonneg_left hk hR
        nlinarith
  have hRbound : R ≤ 2*A*Real.exp (ell*T) := by linarith
  intro t ht
  have he0 : 1 ≤ Real.exp (ell*t) := Real.one_le_exp_iff.mpr (mul_nonneg hell.le ht.1)
  have hft : f t ≤ w t := by
    dsimp [w]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he0 (hnon t ht)
  exact hft.trans ((hmax ht).trans hRbound)

end QuantitativePaper
