module
public import QuantitativeFollowup.PartialFunctionalRegularization

@[expose] public section

/-! The genuine mass-dependent smoothing scale for the sharper quantile
argument. The zero-mass branch has positive width and exactly zero cost. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 600000

def p2SmoothingWidth (r q m : ℝ) : ℝ :=
  if m = 0 then q/8 else Real.sqrt r*q*Real.sqrt q*m

theorem p2SmoothingWidth_pos_le (r q m : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (hm : m ∈ Icc (0 : ℝ) (1/4)) :
    0 < p2SmoothingWidth r q m ∧ p2SmoothingWidth r q m ≤ q/8 := by
  have hqp : 0 < q := hq.1
  have hmn : 0 ≤ m := hm.1
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr.1
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq.1
  have hsr1 : Real.sqrt r ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by simpa using hr.2⟩
  have hsq1 : Real.sqrt q ≤ 1/2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith [hq.2]⟩
  unfold p2SmoothingWidth
  split_ifs with hz
  · exact ⟨by positivity,le_rfl⟩
  · refine ⟨by positivity [lt_of_le_of_ne hm.1 (Ne.symm hz)],?_⟩
    calc
      Real.sqrt r*q*Real.sqrt q*m ≤ 1*q*(1/2)*(1/4) := by
        gcongr <;> first | exact hq.1.le | exact hm.2 | exact hmn | positivity
      _ = q/8 := by ring

theorem p2SmoothingWidth_mem (r q m : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (hm : m ∈ Icc (0 : ℝ) (1/4)) :
    p2SmoothingWidth r q m ∈ Ioc (0 : ℝ) (1-q) := by
  have hh := p2SmoothingWidth_pos_le r q m hr hq hm
  exact ⟨hh.1,hh.2.trans (by linarith [hq.2])⟩

theorem p2SmoothingWidth_exact_cost (r q m : ℝ) (hr : 0 ≤ r) (hq : 0 ≤ q) :
    r*m*(p2SmoothingWidth r q m)^2 = r^2*q^3*m^3 := by
  unfold p2SmoothingWidth
  split_ifs with hz
  · simp [hz]
  · rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hr,Real.sq_sqrt hq]
    ring

theorem p2SmoothingWidth_density_bound (r q m : ℝ) (hr : 0 < r) (hq : 0 < q) (hm : 0 ≤ m) :
    m/p2SmoothingWidth r q m ≤ 1/(Real.sqrt r*q*Real.sqrt q) := by
  unfold p2SmoothingWidth
  split_ifs with hz
  · simp only [hz,zero_div]
    positivity
  · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
    have hden : 0 < Real.sqrt r*q*Real.sqrt q := by positivity
    apply le_of_eq
    field_simp

end QuantitativePaper
