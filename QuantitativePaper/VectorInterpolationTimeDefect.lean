module
public import QuantitativePaper.VectorTemperatureDefectContinuity
public import QuantitativePaper.VectorInterpolationDefectBounds

@[expose] public section

/-! An ordinary real-time representative of the actual defect. The value
outside the physical open interval is only used for interval integration. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativePaper
variable {n : ℕ}

def vectorInterpolationTimeDefect (μ : Paper.ParisiMeasure) (s β t : ℝ) : ℝ :=
  if ht:t<1 then vectorInterpolationDefect (n:=n) μ s β t ht.le else 0

theorem vectorInterpolationTimeDefect_of_lt (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t<1) :
    vectorInterpolationTimeDefect (n:=n) μ s β t=
      vectorInterpolationDefect (n:=n) μ s β t ht.le := by
  simp [vectorInterpolationTimeDefect,ht]

theorem continuousOn_vectorInterpolationTimeDefect (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β : ℝ) (hβ : β≠0) :
    ContinuousOn (vectorInterpolationTimeDefect (n:=n) μ s β) (Iio (1:ℝ)) := by
  apply continuousOn_iff_continuous_restrict.mpr
  exact (continuous_vectorInterpolationDefect_temperature hn μ s β hβ).congr
    fun t=>(vectorInterpolationTimeDefect_of_lt μ s β t t.property).symm

theorem measurable_vectorInterpolationTimeDefect (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β : ℝ) (hβ : β≠0) :
    Measurable (vectorInterpolationTimeDefect (n:=n) μ s β) := by
  have h:=(continuousOn_vectorInterpolationTimeDefect hn μ s β hβ).measurable_piecewise
    (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ=>(0:ℝ)) (Iio (1:ℝ))ᶜ)
    measurableSet_Iio
  convert h using 1
  ext t
  by_cases ht:t<1 <;> simp [Set.piecewise,vectorInterpolationTimeDefect,ht]

theorem vectorInterpolationTimeDefect_bounds (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hs : s≤1) (hβ : β≠0) :
    0≤vectorInterpolationTimeDefect (n:=n) μ s β t ∧
      vectorInterpolationTimeDefect (n:=n) μ s β t≤4*(1-s) := by
  by_cases ht:t<1
  · rw [vectorInterpolationTimeDefect_of_lt μ s β t ht]
    exact vectorInterpolationDefect_bounds hn μ s β t hs hβ ht
  · simp only [vectorInterpolationTimeDefect,dif_neg ht]
    exact ⟨le_rfl,mul_nonneg (by norm_num) (sub_nonneg.mpr hs)⟩

theorem intervalIntegrable_vectorInterpolationTimeDefect (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β : ℝ) (hs : s≤1) (hβ : β≠0) (r u : ℝ) :
    IntervalIntegrable (vectorInterpolationTimeDefect (n:=n) μ s β) volume r u := by
  apply (intervalIntegrable_const (c:=4*(1-s))).mono_fun'
    (measurable_vectorInterpolationTimeDefect hn μ s β hβ).aestronglyMeasurable
  exact .of_forall fun t=>by
    change ‖vectorInterpolationTimeDefect (n:=n) μ s β t‖≤4*(1-s)
    rw [Real.norm_of_nonneg (vectorInterpolationTimeDefect_bounds hn μ s β t hs hβ).1]
    exact (vectorInterpolationTimeDefect_bounds hn μ s β t hs hβ).2

end QuantitativePaper
