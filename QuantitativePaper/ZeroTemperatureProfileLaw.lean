module
public import QuantitativePaper.ScalarFloorContinuity
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Zero-temperature profiles and their genuine bounded-temperature laws.
The values outside `[0,1)` are immaterial to the profile conditions. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ENNReal

namespace QuantitativePaper

/-- The admissible monotone, right-continuous, integrable profile from the source. -/
structure ZeroTemperatureProfile (lam : ℝ) where
  toFun : ℝ → ℝ
  measurable : Measurable toFun
  monotoneOn : MonotoneOn toFun (Ico 0 1)
  lower : ∀ q ∈ Ico 0 1, lam ≤ toFun q
  rightContinuous : ∀ q ∈ Ico 0 1, ContinuousWithinAt toFun (Ici q) q
  intervalIntegrable : IntervalIntegrable toFun volume 0 1

instance instCoeFunZeroTemperatureProfile {lam : ℝ} : CoeFun (ZeroTemperatureProfile lam) (fun _ => ℝ → ℝ) :=
  ⟨ZeroTemperatureProfile.toFun⟩

namespace ZeroTemperatureProfile

/-- Normalize a bounded profile and put the total remaining mass at the terminal endpoint. -/
def normalizedCDF {lam : ℝ} (γ : ZeroTemperatureProfile lam) (β : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x < 1 then γ x / β else 1

@[simp] theorem normalizedCDF_of_mem {lam : ℝ} (γ : ZeroTemperatureProfile lam)
    (β x : ℝ) (hx : x ∈ Ico 0 1) : normalizedCDF γ β x = γ x / β := by
  simp [normalizedCDF, not_lt.mpr hx.1, hx.2]

theorem normalizedCDF_monotone {lam : ℝ} (γ : ZeroTemperatureProfile lam)
    (hLam : 0 ≤ lam) (β : ℝ) (hβ : 0 < β)
    (hupper : ∀ q ∈ Ico 0 1, γ q ≤ β) : Monotone (normalizedCDF γ β) := by
  intro x y hxy
  by_cases hx0 : x < 0
  · by_cases hy0 : y < 0
    · simp [normalizedCDF, hx0, hy0]
    · by_cases hy1 : y < 1
      · simp only [normalizedCDF, hx0, hy0, hy1, ↓reduceIte]
        exact div_nonneg (hLam.trans (γ.lower y ⟨le_of_not_gt hy0, hy1⟩)) hβ.le
      · simp [normalizedCDF, hx0, hy0, hy1]
  · have hx : 0 ≤ x := le_of_not_gt hx0
    have hy0 : ¬ y < 0 := not_lt.mpr (hx.trans hxy)
    by_cases hx1 : x < 1
    · by_cases hy1 : y < 1
      · simp only [normalizedCDF, hx0, hy0, hx1, hy1, ↓reduceIte]
        exact (div_le_div_iff_of_pos_right hβ).mpr (γ.monotoneOn ⟨hx, hx1⟩
          ⟨hx.trans hxy, hy1⟩ hxy)
      · simp only [normalizedCDF, hx0, hy0, hx1, hy1, ↓reduceIte]
        exact (div_le_one hβ).mpr (hupper x ⟨hx, hx1⟩)
    · have hy1 : ¬ y < 1 := not_lt.mpr ((le_of_not_gt hx1).trans hxy)
      simp [normalizedCDF, hx0, hy0, hx1, hy1]

theorem normalizedCDF_rightContinuous {lam : ℝ} (γ : ZeroTemperatureProfile lam)
    (β x : ℝ) : ContinuousWithinAt (normalizedCDF γ β) (Ici x) x := by
  by_cases hx0 : x < 0
  · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq_of_mem ?_ (by simp)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx0)] with y hy
    change y < 0 at hy
    simp [normalizedCDF, hy]
  · by_cases hx1 : x < 1
    · refine ((γ.rightContinuous x ⟨le_of_not_gt hx0, hx1⟩).div_const β).congr_of_eventuallyEq_of_mem ?_ (by simp)
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx1),
        self_mem_nhdsWithin] with y hy hyx
      change y < 1 at hy
      simp [normalizedCDF, not_lt.mpr ((le_of_not_gt hx0).trans hyx), hy]
    · refine (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq_of_mem ?_ (by simp)
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy1 : 1 ≤ y := (le_of_not_gt hx1).trans hy
      simp [normalizedCDF, not_lt.mpr (zero_le_one.trans hy1), not_lt.mpr hy1]

/-- The actual Stieltjes distribution associated with a bounded profile. -/
def stieltjes {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (β : ℝ) (hβ : 0 < β) (hupper : ∀ q ∈ Ico 0 1, γ q ≤ β) :
    StieltjesFunction ℝ where
  toFun := normalizedCDF γ β
  mono' := normalizedCDF_monotone γ hLam β hβ hupper
  right_continuous' := normalizedCDF_rightContinuous γ β

theorem stieltjes_atBot {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (β : ℝ) (hβ : 0 < β) (hupper : ∀ q ∈ Ico 0 1, γ q ≤ β) :
    Tendsto (stieltjes γ hLam β hβ hupper) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  simp [stieltjes, normalizedCDF, hx]

theorem stieltjes_atTop {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (β : ℝ) (hβ : 0 < β) (hupper : ∀ q ∈ Ico 0 1, γ q ≤ β) :
    Tendsto (stieltjes γ hLam β hβ hupper) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simp [stieltjes, normalizedCDF, not_lt.mpr hx, not_lt.mpr (zero_le_one.trans hx)]

/-- A probability law on the physical overlap interval, obtained by an actual measurable map. -/
def parisiMeasure {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (β : ℝ) (hβ : 0 < β) (hupper : ∀ q ∈ Ico 0 1, γ q ≤ β) : Paper.ParisiMeasure := by
  let F := stieltjes γ hLam β hβ hupper
  letI : IsProbabilityMeasure F.measure := F.isProbabilityMeasure
    (stieltjes_atBot γ hLam β hβ hupper) (stieltjes_atTop γ hLam β hβ hupper)
  exact F.measure.toProbabilityMeasure.map (projIcc (0 : ℝ) 1 zero_le_one)

theorem parisiMeasure_cdf {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (β : ℝ) (hβ : 0 < β) (hupper : ∀ q ∈ Ico 0 1, γ q ≤ β)
    (q : ℝ) (hq : q ∈ Ico 0 1) :
    parisiCDF (parisiMeasure γ hLam β hβ hupper) q = γ q / β := by
  have hpre : (projIcc (0 : ℝ) 1 zero_le_one) ⁻¹'
      {r : Paper.Overlap | (r : ℝ) ≤ q} = Iic q := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_Iic]
    constructor
    · intro hx
      by_contra h
      have hqx : q < x := lt_of_not_ge h
      have : q < min (1 : ℝ) x := lt_min hq.2 hqx
      exact (not_lt_of_ge hx) (this.trans_le (le_max_right _ _))
    · intro hx
      exact max_le hq.1 ((min_le_right _ _).trans hx)
  unfold parisiCDF
  change (((stieltjes γ hLam β hβ hupper).measure.map
    (projIcc (0 : ℝ) 1 zero_le_one)) {r : Paper.Overlap | (r : ℝ) ≤ q}).toReal = _
  rw [Measure.map_apply continuous_projIcc.measurable
    (measurableSet_le measurable_subtype_coe measurable_const), hpre,
    StieltjesFunction.measure_Iic _ (stieltjes_atBot γ hLam β hβ hupper)]
  change (ENNReal.ofReal (normalizedCDF γ β q - 0)).toReal = _
  rw [sub_zero, normalizedCDF_of_mem γ β q hq,
    ENNReal.toReal_ofReal (div_nonneg (hLam.trans (γ.lower q hq)) hβ.le)]

theorem parisiMeasure_mem_floor {lam : ℝ} (γ : ZeroTemperatureProfile lam) (hLam : 0 ≤ lam)
    (β : ℝ) (hβ : 0 < β) (hupper : ∀ q ∈ Ico 0 1, γ q ≤ β) :
    parisiMeasure γ hLam β hβ hupper ∈ scalarFloor (lam / β) := by
  rw [mem_scalarFloor_iff, zeroMass_eq_parisiCDF_zero,
    parisiMeasure_cdf γ hLam β hβ hupper 0 (by norm_num)]
  exact (div_le_div_iff_of_pos_right hβ).mpr (γ.lower 0 (by norm_num))

end ZeroTemperatureProfile
end QuantitativePaper
