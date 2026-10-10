module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Deterministic consequences of a square-root response estimate. The
response inequality is an explicit analytic input here; this module does
not assert that a particular Parisi functional satisfies it. The zero
density case is separated, so real division by zero does not replace the
paper's extended-real convention. -/
noncomputable section
namespace FourPapersCommon

theorem response_coercivity_product (F rho A delta Y Z B d : ℝ)
    (hF : 0 ≤ F) (hrho : 0 < rho) (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (_hB : 0 ≤ B) (_hd : 0 ≤ d)
    (hYB : Y ≤ B) (hZd : Z ≤ d * delta)
    (hresponse : A * delta / 2 ≤ Real.sqrt (F / rho) *
      (Real.sqrt Y + 2 * Real.sqrt (Y + Z))) :
    rho * A ^ 2 * delta ^ 2 / 36 ≤ F * (B + d * delta) := by
  have hYZ : 0 ≤ Y + Z := add_nonneg hY hZ
  have hs : Real.sqrt Y ≤ Real.sqrt (Y + Z) := Real.sqrt_le_sqrt (by linarith)
  have hr : A * delta / 2 ≤
      3 * Real.sqrt (F / rho) * Real.sqrt (Y + Z) := by
    calc
      _ ≤ Real.sqrt (F / rho) * (Real.sqrt Y + 2 * Real.sqrt (Y + Z)) :=
        hresponse
      _ ≤ Real.sqrt (F / rho) * (3 * Real.sqrt (Y + Z)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hsq : (A * delta / 2) ^ 2 ≤ 9 * (F / rho) * (Y + Z) := by
    calc
      _ ≤ (3 * Real.sqrt (F / rho) * Real.sqrt (Y + Z)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hr 2
      _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hF hrho.le),
          Real.sq_sqrt hYZ]
        ring
  have hc : rho * (A * delta / 2) ^ 2 ≤ 9 * F * (Y + Z) := by
    have he : 9 * (F / rho) * (Y + Z) = (9 * F * (Y + Z)) / rho := by ring
    rw [he] at hsq
    convert (le_div_iff₀ hrho).mp hsq using 1
    ring
  have hm : F * (Y + Z) ≤ F * (B + d * delta) :=
    mul_le_mul_of_nonneg_left (add_le_add hYB hZd) hF
  nlinarith

/-- Literal minimum bound when the density bound is positive. -/
theorem response_coercivity (F rho A delta Y Z B d : ℝ)
    (hF : 0 ≤ F) (hrho : 0 < rho) (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hB : 0 < B) (hd : 0 < d)
    (hYB : Y ≤ B) (hZd : Z ≤ d * delta)
    (hresponse : A * delta / 2 ≤ Real.sqrt (F / rho) *
      (Real.sqrt Y + 2 * Real.sqrt (Y + Z))) :
    rho * A ^ 2 / 72 * min (delta ^ 2 / B) (delta / d) ≤ F := by
  have hc := response_coercivity_product F rho A delta Y Z B d
    hF hrho hA hdelta hY hZ hB.le hd.le hYB hZd hresponse
  have hfactor : 0 ≤ rho * A ^ 2 / 72 := by positivity
  by_cases hcase : d * delta ≤ B
  · have hm : F * (B + d * delta) ≤ 2 * F * B := by nlinarith
    have hfirst : rho * A ^ 2 / 72 * (delta ^ 2 / B) ≤ F := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hB).mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hfactor).trans hfirst
  · have hdeltaPos : 0 < delta := by
      have : 0 < d * delta := hB.trans (lt_of_not_ge hcase)
      exact pos_of_mul_pos_right this hd.le
    have hden : 0 < d * delta := mul_pos hd hdeltaPos
    have hm : F * (B + d * delta) ≤ 2 * F * (d * delta) := by
      nlinarith [lt_of_not_ge hcase]
    have hsecond : rho * A ^ 2 / 72 * (delta / d) ≤ F := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hd).mpr
      have hm' : (rho * A ^ 2 / 72 * delta) * delta ≤ (F * d) * delta := by
        nlinarith
      exact (mul_le_mul_iff_left₀ hdeltaPos).mp hm'
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hfactor).trans hsecond

/-- If the density bound is zero, its entry in the extended-real minimum
is infinite for positive delta. This stronger real-valued bound is valid
also at delta zero. -/
theorem response_coercivity_zero_density (F rho A delta Y Z B : ℝ)
    (hF : 0 ≤ F) (hrho : 0 < rho) (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hB : 0 < B)
    (hYB : Y ≤ B) (hZd : Z ≤ 0)
    (hresponse : A * delta / 2 ≤ Real.sqrt (F / rho) *
      (Real.sqrt Y + 2 * Real.sqrt (Y + Z))) :
    rho * A ^ 2 * delta ^ 2 / (36 * B) ≤ F := by
  have hc := response_coercivity_product F rho A delta Y Z B 0
    hF hrho hA hdelta hY hZ hB.le le_rfl hYB (by simpa using hZd) hresponse
  simp only [zero_mul, add_zero] at hc
  apply (div_le_iff₀ (mul_pos (by norm_num) hB)).mpr
  nlinarith

theorem coercivity_min_monotone (B d : ℝ) (hB : 0 < B) (hd : 0 < d)
    {delta₀ delta₁ : ℝ} (hdelta₀ : 0 ≤ delta₀) (hle : delta₀ ≤ delta₁) :
    min (delta₀ ^ 2 / B) (delta₀ / d) ≤
      min (delta₁ ^ 2 / B) (delta₁ / d) := by
  apply min_le_min
  · exact (div_le_div_iff_of_pos_right hB).mpr (by nlinarith)
  · exact (div_le_div_iff_of_pos_right hd).mpr hle

end FourPapersCommon
