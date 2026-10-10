module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

/-! The actual height-one triangular cutoff on an interval. -/
noncomputable section
open Set MeasureTheory intervalIntegral
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1200000

def triangleCutoff (a ell x : ℝ) : ℝ :=
  max 0 (min ((2 / ell) * (x - a)) ((2 / ell) * (a + ell - x)))

theorem triangleCutoff_nonneg (a ell x : ℝ) : 0 ≤ triangleCutoff a ell x := le_max_left _ _

theorem triangleCutoff_le_one (a ell x : ℝ) (hell : 0 < ell) :
    triangleCutoff a ell x ≤ 1 := by
  unfold triangleCutoff
  apply max_le zero_le_one
  have he : (2 / ell) * (x - a) + (2 / ell) * (a + ell - x) = 2 := by
    field_simp
    ring
  by_cases hl : (2 / ell) * (x - a) ≤ 1
  · exact (min_le_left _ _).trans hl
  · exact (min_le_right _ _).trans (by linarith)

theorem triangleCutoff_eq_left (a ell x : ℝ) (hell : 0 < ell)
    (hx : x ∈ Icc a (a + ell / 2)) :
    triangleCutoff a ell x = (2 / ell) * (x - a) := by
  unfold triangleCutoff
  rw [min_eq_left (mul_le_mul_of_nonneg_left (by linarith [hx.2]) (by positivity)),
    max_eq_right (mul_nonneg (by positivity) (sub_nonneg.mpr hx.1))]

theorem triangleCutoff_eq_right (a ell x : ℝ) (hell : 0 < ell)
    (hx : x ∈ Icc (a + ell / 2) (a + ell)) :
    triangleCutoff a ell x = (2 / ell) * (a + ell - x) := by
  unfold triangleCutoff
  rw [min_eq_right (mul_le_mul_of_nonneg_left (by linarith [hx.1]) (by positivity)),
    max_eq_right (mul_nonneg (by positivity) (sub_nonneg.mpr hx.2))]

theorem triangleCutoff_zero_outside (a ell x : ℝ) (hell : 0 < ell)
    (hx : x ∉ Ioo a (a + ell)) : triangleCutoff a ell x = 0 := by
  unfold triangleCutoff
  apply max_eq_left
  by_cases hxa : x ≤ a
  · exact (min_le_left _ _).trans (mul_nonpos_of_nonneg_of_nonpos
      (by positivity) (sub_nonpos.mpr hxa))
  · have hax : a < x := lt_of_not_ge hxa
    have hxe : a + ell ≤ x := le_of_not_gt (fun hh => hx ⟨hax, hh⟩)
    exact (min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos
      (by positivity) (sub_nonpos.mpr hxe))

theorem triangleCutoff_lipschitz (a ell : ℝ) (hell : 0 < ell) :
    LipschitzWith (Real.toNNReal (2 / ell)) (triangleCutoff a ell) := by
  have hl : LipschitzWith (Real.toNNReal (2 / ell))
      (fun x : ℝ => (2 / ell) * (x - a)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have he : (2 / ell) * (x - a) - (2 / ell) * (y - a) = (2 / ell) * (x - y) := by ring
    rw [he, abs_mul, abs_of_pos (by positivity)]
  have hr : LipschitzWith (Real.toNNReal (2 / ell))
      (fun x : ℝ => (2 / ell) * (a + ell - x)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have he : (2 / ell) * (a + ell - x) - (2 / ell) * (a + ell - y) =
        (2 / ell) * (y - x) := by ring
    rw [he, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
  change LipschitzWith (Real.toNNReal (2 / ell))
    (fun x => max 0 (min ((2 / ell) * (x - a)) ((2 / ell) * (a + ell - x))))
  simpa only [max_self] using (hl.min hr).const_max 0

theorem continuous_triangleCutoff (a ell : ℝ) (hell : 0 < ell) :
    Continuous (triangleCutoff a ell) := (triangleCutoff_lipschitz a ell hell).continuous

theorem triangleCutoff_interval_integral (a ell : ℝ) (hell : 0 < ell) :
    (∫ x in a..(a + ell), triangleCutoff a ell x) = ell / 2 := by
  let m := a + ell / 2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hme : m ≤ a + ell := by dsimp [m]; linarith
  have hi₁ := (continuous_triangleCutoff a ell hell).intervalIntegrable (μ := volume) a m
  have hi₂ := (continuous_triangleCutoff a ell hell).intervalIntegrable (μ := volume) m (a + ell)
  rw [← integral_add_adjacent_intervals hi₁ hi₂]
  have he₁ : (∫ x in a..m, triangleCutoff a ell x) = ell / 4 := by
    rw [integral_congr_Ioo_of_le ham (fun x hx => triangleCutoff_eq_left a ell x hell
      ⟨hx.1.le, hx.2.le⟩), intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => a)
        (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const]
    dsimp only [m]
    field_simp
    ring
  have he₂ : (∫ x in m..(a + ell), triangleCutoff a ell x) = ell / 4 := by
    rw [integral_congr_Ioo_of_le hme (fun x hx => triangleCutoff_eq_right a ell x hell
      ⟨hx.1.le, hx.2.le⟩), intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => a + ell) (g := fun x : ℝ => x)
        intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      integral_id, intervalIntegral.integral_const]
    dsimp only [m]
    field_simp
    ring
  rw [he₁, he₂]
  ring

end FourPapersCommon
