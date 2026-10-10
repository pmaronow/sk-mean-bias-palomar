module
public import FourPapersCommon.TriangleCutoff
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section

/-! Actual a.e. derivative, area, and Dirichlet energy of the triangular
cutoff. The three corners are removed using genuine Lebesgue null sets. -/
noncomputable section
open Set MeasureTheory Filter intervalIntegral
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1500000

theorem hasDerivAt_triangleCutoff_left (a ell x : ℝ) (hell : 0 < ell)
    (hx : x ∈ Ioo a (a + ell / 2)) :
    HasDerivAt (triangleCutoff a ell) (2 / ell) x := by
  have hd : HasDerivAt (fun y : ℝ => (2 / ell) * (y - a)) (2 / ell) x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).sub_const a).const_mul (2 / ell)
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact triangleCutoff_eq_left a ell y hell ⟨hy.1.le, hy.2.le⟩

theorem hasDerivAt_triangleCutoff_right (a ell x : ℝ) (hell : 0 < ell)
    (hx : x ∈ Ioo (a + ell / 2) (a + ell)) :
    HasDerivAt (triangleCutoff a ell) (-(2 / ell)) x := by
  have hd : HasDerivAt (fun y : ℝ => (2 / ell) * (a + ell - y)) (-(2 / ell)) x := by
    convert! ((hasDerivAt_const x (a + ell)).sub (hasDerivAt_id x)).const_mul (2 / ell) using 1
    simp only [zero_sub, mul_neg, mul_one]
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact triangleCutoff_eq_right a ell y hell ⟨hy.1.le, hy.2.le⟩

theorem hasDerivAt_triangleCutoff_zero_left (a ell x : ℝ) (hell : 0 < ell) (hx : x < a) :
    HasDerivAt (triangleCutoff a ell) 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact triangleCutoff_zero_outside a ell y hell (fun hz => (not_lt_of_ge hy.le) hz.1)

theorem hasDerivAt_triangleCutoff_zero_right (a ell x : ℝ) (hell : 0 < ell)
    (hx : a + ell < x) : HasDerivAt (triangleCutoff a ell) 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact triangleCutoff_zero_outside a ell y hell (fun hz => (not_lt_of_ge hy.le) hz.2)

theorem deriv_triangleCutoff_sq_ae (a ell : ℝ) (hell : 0 < ell) :
    (fun x => (deriv (triangleCutoff a ell) x) ^ 2) =ᵐ[volume]
      (Ioo a (a + ell)).indicator (fun _ : ℝ => (2 / ell) ^ 2) := by
  filter_upwards [volume.ae_ne a, volume.ae_ne (a + ell / 2), volume.ae_ne (a + ell)]
    with x hxa hxm hxe
  by_cases hx : x ∈ Ioo a (a + ell)
  · rw [indicator_of_mem hx]
    by_cases hleft : x < a + ell / 2
    · rw [(hasDerivAt_triangleCutoff_left a ell x hell ⟨hx.1, hleft⟩).deriv]
    · have hright : a + ell / 2 < x := lt_of_le_of_ne (le_of_not_gt hleft) hxm.symm
      rw [(hasDerivAt_triangleCutoff_right a ell x hell ⟨hright, hx.2⟩).deriv]
      ring
  · rw [indicator_of_notMem hx]
    by_cases hleft : x < a
    · rw [(hasDerivAt_triangleCutoff_zero_left a ell x hell hleft).deriv]
      norm_num
    · have hax : a < x := lt_of_le_of_ne (le_of_not_gt hleft) hxa.symm
      have he : a + ell < x := lt_of_le_of_ne (le_of_not_gt (fun h => hx ⟨hax, h⟩)) hxe.symm
      rw [(hasDerivAt_triangleCutoff_zero_right a ell x hell he).deriv]
      norm_num

theorem ae_differentiableAt_triangleCutoff (a ell : ℝ) (hell : 0 < ell) :
    ∀ᵐ x ∂ volume, DifferentiableAt ℝ (triangleCutoff a ell) x := by
  filter_upwards [volume.ae_ne a, volume.ae_ne (a + ell / 2), volume.ae_ne (a + ell)]
    with x hxa hxm hxe
  by_cases hx : x ∈ Ioo a (a + ell)
  · by_cases hleft : x < a + ell / 2
    · exact (hasDerivAt_triangleCutoff_left a ell x hell ⟨hx.1, hleft⟩).differentiableAt
    · exact (hasDerivAt_triangleCutoff_right a ell x hell
        ⟨lt_of_le_of_ne (le_of_not_gt hleft) hxm.symm, hx.2⟩).differentiableAt
  · by_cases hleft : x < a
    · exact (hasDerivAt_triangleCutoff_zero_left a ell x hell hleft).differentiableAt
    · have hax : a < x := lt_of_le_of_ne (le_of_not_gt hleft) hxa.symm
      have he : a + ell < x := lt_of_le_of_ne (le_of_not_gt (fun h => hx ⟨hax, h⟩)) hxe.symm
      exact (hasDerivAt_triangleCutoff_zero_right a ell x hell he).differentiableAt

theorem triangleCutoff_energy_intervalIntegrable (a ell : ℝ) (hell : 0 < ell) :
    IntervalIntegrable (fun x => (deriv (triangleCutoff a ell) x) ^ 2) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  refine Integrable.of_bound ((measurable_deriv (triangleCutoff a ell)).pow_const 2).aestronglyMeasurable
    ((2 / ell) ^ 2) (.of_forall fun x => ?_)
  have hh := norm_deriv_le_of_lipschitz (x₀ := x) (triangleCutoff_lipschitz a ell hell)
  rw [Real.coe_toNNReal _ (by positivity)] at hh
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem triangleCutoff_integral_unit (a ell : ℝ) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a + ell ≤ 1) :
    (∫ x in (0 : ℝ)..1, triangleCutoff a ell x) = ell / 2 := by
  have hsub : Ioo a (a + ell) ⊆ Ioc (0 : ℝ) 1 :=
    fun x hx => ⟨ha.trans_lt hx.1, hx.2.le.trans he⟩
  have hf : triangleCutoff a ell = (Ioo a (a + ell)).indicator (triangleCutoff a ell) := by
    funext x
    by_cases hx : x ∈ Ioo a (a + ell)
    · exact (indicator_of_mem hx _).symm
    · rw [indicator_of_notMem hx, triangleCutoff_zero_outside a ell x hell hx]
  rw [intervalIntegral.integral_of_le zero_le_one, hf,
    MeasureTheory.integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hsub]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show a ≤ a + ell by linarith)]
  exact triangleCutoff_interval_integral a ell hell

theorem triangleCutoff_energy_unit (a ell : ℝ) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a + ell ≤ 1) :
    (∫ x in (0 : ℝ)..1, (deriv (triangleCutoff a ell) x) ^ 2) = 4 / ell := by
  have hsub : Ioo a (a + ell) ⊆ Ioc (0 : ℝ) 1 :=
    fun x hx => ⟨ha.trans_lt hx.1, hx.2.le.trans he⟩
  rw [intervalIntegral.integral_of_le zero_le_one,
    integral_congr_ae (ae_restrict_of_ae (deriv_triangleCutoff_sq_ae a ell hell)),
    MeasureTheory.integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hsub, MeasureTheory.integral_const]
  rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (show 0 ≤ a + ell - a by linarith)]
  simp only [smul_eq_mul]
  field_simp
  ring

end FourPapersCommon
