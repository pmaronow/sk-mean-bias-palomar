module
public import QuantitativePaper.ZeroTemperatureProfileLawRaw

@[expose] public section

/-! Actual Parisi CDFs and truncation preserve zero-temperature admissibility. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ENNReal
namespace QuantitativePaper.ZeroTemperatureProfile

/-- The actual profile corresponding to any admissible scalar-floor measure. -/
def ofParisiMeasure (lam β : ℝ) (hβ : 0 < β) (μ : Paper.ParisiMeasure)
    (hfloor : μ ∈ scalarFloor (lam / β)) : ZeroTemperatureProfile lam where
  toFun q := β * parisiCDF μ q
  measurable := measurable_const.mul (parisiCDF_measurable μ)
  monotoneOn := ((parisiCDF_monotone μ).const_mul hβ.le).monotoneOn _
  lower := by
    intro q hq
    have hl := scalarFloor_cdf_lower hfloor hq.1
    have he : lam = β * (lam / β) := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hl hβ.le
  rightContinuous := fun q _ => (FRSB.parisiCDF_right_continuous μ q).const_mul β
  intervalIntegrable := (parisiCDF_intervalIntegrable μ 0 1).const_mul β

@[simp] theorem ofParisiMeasure_apply (lam β : ℝ) (hβ : 0 < β)
    (μ : Paper.ParisiMeasure) (hfloor : μ ∈ scalarFloor (lam / β)) (q : ℝ) :
    ofParisiMeasure lam β hβ μ hfloor q = β * parisiCDF μ q := rfl

theorem ofParisiMeasure_upper (lam β : ℝ) (hβ : 0 < β)
    (μ : Paper.ParisiMeasure) (hfloor : μ ∈ scalarFloor (lam / β)) (q : ℝ) :
    ofParisiMeasure lam β hβ μ hfloor q ≤ β := by
  change β * parisiCDF μ q ≤ β
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (parisiCDF_le_one μ q) hβ.le

/-- The literal nonnegative clamp used for the source's monotone truncations. -/
def truncatedFun {lam : ℝ} (γ : ZeroTemperatureProfile lam) (R q : ℝ) : ℝ :=
  min (max 0 (γ q)) (max 0 R)

theorem measurable_truncatedFun {lam : ℝ} (γ : ZeroTemperatureProfile lam) (R : ℝ) :
    Measurable (truncatedFun γ R) :=
  (measurable_const.max γ.measurable).min measurable_const

theorem truncatedFun_nonneg {lam : ℝ} (γ : ZeroTemperatureProfile lam) (R q : ℝ) :
    0 ≤ truncatedFun γ R q :=
  le_min (le_max_left _ _) (le_max_left _ _)

theorem truncatedFun_le {lam : ℝ} (γ : ZeroTemperatureProfile lam) (R : ℝ)
    (hR : 0 ≤ R) (q : ℝ) : truncatedFun γ R q ≤ R := by
  unfold truncatedFun
  rw [max_eq_right hR]
  exact min_le_right _ _

/-- Bounded nonnegative truncation remains in the same admissible profile class. -/
def truncate {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (R : ℝ) (hR : lam ≤ R) : ZeroTemperatureProfile lam where
  toFun := truncatedFun γ R
  measurable := measurable_truncatedFun γ R
  monotoneOn := by
    intro x hx y hy hxy
    exact min_le_min (max_le_max le_rfl (γ.monotoneOn hx hy hxy)) le_rfl
  lower := by
    intro q hq
    exact le_min ((γ.lower q hq).trans (le_max_right _ _)) (hR.trans (le_max_right _ _))
  rightContinuous := fun q hq =>
    (continuousWithinAt_const.max (γ.rightContinuous q hq)).min continuousWithinAt_const
  intervalIntegrable := by
    refine (intervalIntegrable_const (c := R)).mono_fun'
      (measurable_truncatedFun γ R).aestronglyMeasurable ?_
    filter_upwards [] with q
    rw [Real.norm_eq_abs, abs_of_nonneg (truncatedFun_nonneg γ R q)]
    exact truncatedFun_le γ R (hLam.trans hR) q

@[simp] theorem truncate_apply {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (R : ℝ) (hR : lam ≤ R) (q : ℝ) :
    truncate γ hLam R hR q = min (max 0 (γ q)) (max 0 R) := rfl

theorem truncate_eqOn {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (R : ℝ) (hR : lam ≤ R) : EqOn (truncate γ hLam R hR) (fun q => min (γ q) R) (Ico 0 1) := by
  intro q hq
  simp only [truncate_apply, max_eq_right (hLam.trans (γ.lower q hq)),
    max_eq_right (hLam.trans hR)]

theorem truncate_upper {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (R : ℝ) (hR : lam ≤ R) (q : ℝ) : truncate γ hLam R hR q ≤ R :=
  truncatedFun_le γ R (hLam.trans hR) q

end QuantitativePaper.ZeroTemperatureProfile
