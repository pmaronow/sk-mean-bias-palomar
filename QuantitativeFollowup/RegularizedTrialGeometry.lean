module
public import QuantitativeFollowup.ReflectedRegularization
public import QuantitativeFollowup.ScalarTrialMeasure
public import QuantitativeFollowup.ScalarTrialDensity
public import FourPapersCommon.CDFDistanceTriangle
public import Mathlib.Tactic

@[expose] public section

/-! Actual profile geometry of the reflected minimizer-to-scalar-trial
segment. Root values, one-sided slope, post-support monotonicity, and
global bounds are derived from the constructed probability measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB QuantitativePaper
open scoped ENNReal NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

theorem reflected_profile_increment_le (β : ℝ) (hβ : 0 ≤ β)
    (μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) (1 / 2)) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    β * (parisiCDF (reflectedParisiMeasure μ s h hs hh.1) y -
      parisiCDF (reflectedParisiMeasure μ s h hs hh.1) x) ≤ (β / h) * (y - x) := by
  let ν := reflectedParisiMeasure μ s h hs hh.1
  let P : Measure ℝ := (ν : Measure Paper.Overlap).map Subtype.val
  have he : P (Ioc x y) = ENNReal.ofReal (parisiCDF ν y - parisiCDF ν x) := by
    rw [← measure_cdf P, StieltjesFunction.measure_Ioc]
    exact congrArg ENNReal.ofReal (congrArg₂ (fun a b : ℝ => a - b)
      (parisiCDF_eq_realCDF ν y).symm (parisiCDF_eq_realCDF ν x).symm)
  have hf : P (Ioc x y) =
      (reflectedFreeMeasure μ s h).map (Subtype.val : Paper.Overlap → ℝ) (Ioc x y) := by
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Ioc,
      Measure.map_apply measurable_subtype_coe measurableSet_Ioc]
    change reflectedOverlapMeasure μ s h (Subtype.val ⁻¹' Ioc x y) = _
    have hz : zeroOverlap ∉ (Subtype.val : Paper.Overlap → ℝ) ⁻¹' Ioc x y :=
      fun hz => (not_lt_of_ge hx) hz.1
    rw [reflectedOverlapMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' zeroOverlap (measurable_subtype_coe measurableSet_Ioc),
      indicator_of_notMem hz, smul_zero, zero_add]
  have hd := reflectedFreeMeasure_density_le μ s h hs hh (Ioc x y)
  rw [← hf, he, Measure.smul_apply, smul_eq_mul, Real.volume_Ioc,
    ← ENNReal.ofReal_mul (div_nonneg (sub_nonneg.mpr hs.2) hh.1.le)] at hd
  have hnonneg : 0 ≤ parisiCDF ν y - parisiCDF ν x :=
    sub_nonneg.mpr (parisiCDF_monotone ν hxy)
  have hrhs : 0 ≤ ((1 - s) / h) * (y - x) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hs.2) hh.1.le) (sub_nonneg.mpr hxy)
  have hdreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  rw [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal hrhs] at hdreal
  have hsmall : ((1 - s) / h) * (y - x) ≤ (1 / h) * (y - x) := by
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hxy)
    apply (div_le_div_iff_of_pos_right hh.1).mpr
    linarith [hs.1]
  calc
    _ ≤ β * ((1 / h) * (y - x)) := mul_le_mul_of_nonneg_left (hdreal.trans hsmall) hβ
    _ = _ := by ring

theorem reflected_profile_lipschitzOn (β : ℝ) (hβ : 0 ≤ β)
    (μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) (1 / 2)) :
    LipschitzOnWith (Real.toNNReal (β / h))
      (fun x => β * parisiCDF (reflectedParisiMeasure μ s h hs hh.1) x) (Ici (0 : ℝ)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (div_nonneg hβ hh.1.le)]
  by_cases hxy : x ≤ y
  · rw [abs_sub_comm (β * _), abs_sub_comm x, ← mul_sub,
      abs_of_nonneg (mul_nonneg hβ (sub_nonneg.mpr (parisiCDF_monotone _ hxy))),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact reflected_profile_increment_le β hβ μ s h hs hh x y hx hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [← mul_sub,
      abs_of_nonneg (mul_nonneg hβ (sub_nonneg.mpr (parisiCDF_monotone _ hyx))),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact reflected_profile_increment_le β hβ μ s h hs hh y x hy hyx

def regularizedTrialDifference (β lam : ℝ) (scalar μ : Paper.ParisiMeasure)
    (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (x : ℝ) : ℝ :=
  scalarTrialProfile β lam scalar x - β * parisiCDF (reflectedParisiMeasure μ s h hs hh) x

theorem regularizedTrialDifference_initial (β : ℝ) (hβ : β ≠ 0)
    (scalar μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 scalar)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (hsupp : parisiSupport scalar = Icc (0 : ℝ) q)
    (lam s h : ℝ) (hlam : 0 ≤ lam) (hs : s ∈ Icc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) (1 / 2)) (hroot : β * s = lam) :
    regularizedTrialDifference β lam scalar μ s h hs hh.1 0 = 0 := by
  rw [regularizedTrialDifference, scalar_trial_initial β hβ scalar hmin q hq hsupp lam hlam,
    reflected_energy_root β μ s h hs hh, hroot, sub_self]

theorem regularizedTrialDifference_norm_le (β lam : ℝ) (hβ : 0 ≤ β)
    (hlam : lam ∈ Icc (0 : ℝ) β) (scalar μ : Paper.ParisiMeasure)
    (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (x : ℝ) :
    |regularizedTrialDifference β lam scalar μ s h hs hh x| ≤ β := by
  have ha : 0 ≤ scalarTrialProfile β lam scalar x :=
    hlam.1.trans (le_max_left _ _)
  have hb : scalarTrialProfile β lam scalar x ≤ β := by
    apply max_le hlam.2
    nlinarith [parisiCDF_le_one scalar x]
  have hc := parisiCDF_nonneg (reflectedParisiMeasure μ s h hs hh) x
  have hd := parisiCDF_le_one (reflectedParisiMeasure μ s h hs hh) x
  rw [abs_le]
  dsimp only [regularizedTrialDifference]
  constructor <;> nlinarith

theorem regularizedTrialDifference_post_terminal (β lam : ℝ) (hβ : 0 ≤ β)
    (hlam : lam ≤ β) (scalar μ : Paper.ParisiMeasure) (q : ℝ)
    (hsupp : parisiSupport scalar = Icc (0 : ℝ) q)
    (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hh : 0 < h) :
    (∀ x ∈ Ici q, 0 ≤ regularizedTrialDifference β lam scalar μ s h hs hh x) ∧
    AntitoneOn (regularizedTrialDifference β lam scalar μ s h hs hh) (Ici q) := by
  have he (x : ℝ) (hx : q ≤ x) :
      regularizedTrialDifference β lam scalar μ s h hs hh x =
        β - β * parisiCDF (reflectedParisiMeasure μ s h hs hh) x := by
    rw [regularizedTrialDifference, scalar_trial_terminal β lam scalar q hsupp hlam x hx]
  constructor
  · intro x hx
    rw [he x hx]
    nlinarith [parisiCDF_le_one (reflectedParisiMeasure μ s h hs hh) x]
  · intro x hx y hy hxy
    rw [he x hx, he y hy]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (parisiCDF_monotone _ hxy) hβ) β

theorem regularizedTrialDifference_slope (β : ℝ) (hβ : 0 < β)
    (scalar μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 scalar)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (hsupp : parisiSupport scalar = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lam s h : ℝ, ∀ hs : s ∈ Icc (0 : ℝ) 1,
      ∀ hh : 0 < h, ∀ z x : ℝ, 0 ≤ z → z ≤ x → x < q →
        regularizedTrialDifference β lam scalar μ s h hs hh x -
          regularizedTrialDifference β lam scalar μ s h hs hh z ≤ L * (x - z) := by
  obtain ⟨L, hL, hLip⟩ := scalar_trial_lipschitz_below_terminal β hβ scalar hmin q hq hsupp
  refine ⟨L, hL, ?_⟩
  intro lam s h hs hh z x hz hzx hx
  have hv := hLip lam z x ⟨hz, hzx.trans_lt hx⟩ ⟨hz.trans hzx, hx⟩
  simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hzx)] at hv
  have hmono := parisiCDF_monotone (reflectedParisiMeasure μ s h hs hh) hzx
  have hm := mul_le_mul_of_nonneg_left hmono hβ.le
  dsimp only [regularizedTrialDifference]
  linarith [le_abs_self (scalarTrialProfile β lam scalar x - scalarTrialProfile β lam scalar z)]

theorem regularizedTrialDifference_continuous_post_terminal (β lam : ℝ)
    (hβ : 0 ≤ β) (hlam : lam ≤ β) (scalar μ : Paper.ParisiMeasure) (q : ℝ)
    (hq : 0 ≤ q) (hsupp : parisiSupport scalar = Icc (0 : ℝ) q)
    (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) (1 / 2)) :
    ContinuousOn (regularizedTrialDifference β lam scalar μ s h hs hh.1) (Ici q) := by
  have hc := (reflected_profile_lipschitzOn β hβ μ s h hs hh).continuousOn
  apply ((continuousOn_const (c := β)).sub (hc.mono (fun x hx => hq.trans hx))).congr
  intro x hx
  rw [regularizedTrialDifference, scalar_trial_terminal β lam scalar q hsupp hlam x hx]
  rfl

theorem scalarClippedTrialMeasure_energy_cdf (β : ℝ) (hβ : 0 ≤ β)
    (scalar : Paper.ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    β * parisiCDF (scalarClippedTrialMeasure s hs scalar) x =
      scalarTrialProfile β (β * s) scalar x := by
  rw [scalarClippedTrialMeasure_cdf s hs scalar x hx, mul_max_of_nonneg _ _ hβ]
  rfl

theorem regularizedTrialDifference_integral_abs (β : ℝ) (hβ : 0 ≤ β)
    (scalar μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hh : 0 < h) :
    (∫ x in (0 : ℝ)..1, |regularizedTrialDifference β (β * s) scalar μ s h hs hh x|) =
      β * parisiCDFDistance (reflectedParisiMeasure μ s h hs hh)
        (scalarClippedTrialMeasure s hs scalar) := by
  rw [parisiCDFDistance, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hx
  change |scalarTrialProfile β (β * s) scalar x -
      β * parisiCDF (reflectedParisiMeasure μ s h hs hh) x| =
    β * |parisiCDF (reflectedParisiMeasure μ s h hs hh) x -
      parisiCDF (scalarClippedTrialMeasure s hs scalar) x|
  rw [← scalarClippedTrialMeasure_energy_cdf β hβ scalar s hs x hx',
    ← mul_sub, abs_mul, abs_of_nonneg hβ, abs_sub_comm]

theorem regularizedTrialDifference_distance_lower (β : ℝ) (hβ : 0 ≤ β)
    (scalar μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor s) (hh : h ∈ Ioc (0 : ℝ) (1 / 2)) :
    β * parisiCDFDistance μ (scalarClippedTrialMeasure s hs scalar) - β * h ≤
      ∫ x in (0 : ℝ)..1, |regularizedTrialDifference β (β * s) scalar μ s h hs hh.1 x| := by
  rw [regularizedTrialDifference_integral_abs β hβ scalar μ s h hs hh.1]
  have ht := mul_le_mul_of_nonneg_left (FourPapersCommon.parisiCDFDistance_triangle μ
    (reflectedParisiMeasure μ s h hs hh.1) (scalarClippedTrialMeasure s hs scalar)) hβ
  have hr := reflected_energy_cdfDistance_le β hβ μ s h hs hμ hh
  linarith

theorem regularizedTrialDifference_distance_half (β : ℝ) (hβ : 0 ≤ β)
    (scalar μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor s) (hh : h ∈ Ioc (0 : ℝ) (1 / 2))
    (hsmall : 2 * β * h ≤ β * parisiCDFDistance μ (scalarClippedTrialMeasure s hs scalar)) :
    β * parisiCDFDistance μ (scalarClippedTrialMeasure s hs scalar) / 2 ≤
      ∫ x in (0 : ℝ)..1, |regularizedTrialDifference β (β * s) scalar μ s h hs hh.1 x| := by
  linarith [regularizedTrialDifference_distance_lower β hβ scalar μ s h hs hμ hh]

end QuantitativeFollowup
