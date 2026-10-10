module
public import QuantitativePaper.VectorMeasureFunctional

@[expose] public section

/-! Genuine weak continuity and constrained compact attainment for the
constructed interpolating vector functional. Contact and differentiability
of the minimizing envelope are separate obligations. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativePaper

theorem continuous_vectorMeasureFunctional (n : ℕ) (hn : 0<n) (β t a : ℝ) (ht : t ≤ 1) :
    Continuous (fun μ => vectorMeasureFunctional n μ β t a) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun ν => norm_nonneg _)
    (fun ν => by simpa only [Real.norm_eq_abs] using
      vectorMeasureFunctional_CDFDistance_abs_sub_le n hn ν μ β t a ht)
  simpa only [mul_zero,id_eq] using
    (FRSB.tendsto_parisiCDFDistance_of_tendsto (μ:=μ) tendsto_id).const_mul
      ((3/2 : ℝ)*((1-t)*β^2))

theorem exists_vectorMeasure_minimizer (n : ℕ) (hn : 0<n) (β t a : ℝ) (ht : t ≤ 1)
    (ha : a ≤ 1) :
    ∃μ∈scalarFloor a,∀ν∈scalarFloor a,
      vectorMeasureFunctional n μ β t a ≤ vectorMeasureFunctional n ν β t a :=
  (isCompact_scalarFloor a).exists_isMinOn (scalarFloor_nonempty a ha)
    (continuous_vectorMeasureFunctional n hn β t a ht).continuousOn

def vectorMeasureMinimizer (n : ℕ) (hn : 0<n) (β t a : ℝ) (ht : t ≤ 1) (ha : a ≤ 1) :
    Paper.ParisiMeasure :=
  Classical.choose (exists_vectorMeasure_minimizer n hn β t a ht ha)

theorem vectorMeasureMinimizer_mem (n : ℕ) (hn : 0<n) (β t a : ℝ) (ht : t ≤ 1) (ha : a ≤ 1) :
    vectorMeasureMinimizer n hn β t a ht ha∈scalarFloor a :=
  (Classical.choose_spec (exists_vectorMeasure_minimizer n hn β t a ht ha)).1

theorem vectorMeasureMinimizer_minimal (n : ℕ) (hn : 0<n) (β t a : ℝ) (ht : t ≤ 1) (ha : a ≤ 1)
    (ν : Paper.ParisiMeasure) (hν : ν∈scalarFloor a) :
    vectorMeasureFunctional n (vectorMeasureMinimizer n hn β t a ht ha) β t a ≤
      vectorMeasureFunctional n ν β t a :=
  (Classical.choose_spec (exists_vectorMeasure_minimizer n hn β t a ht ha)).2 ν hν

end QuantitativePaper
