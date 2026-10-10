module
public import QuantitativePaper.VectorDyadicGridJetAgreement
public import QuantitativePaper.VectorMeasureFunctional
public import QuantitativePaper.VectorMeasureDisorderTilt

@[expose] public section

/-! Actual outer law and full functional agreement on nested dyadic grids. -/
noncomputable section
open MeasureTheory
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem vectorMeasureOuterWeight_grid_eq_finite (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t a : ℝ) (ht : t ≤ 1) :
    vectorMeasureOuterWeight (n := n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a =
      vectorOuterWeight (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  unfold vectorMeasureOuterWeight vectorOuterWeight vectorMeasureOuterPartition vectorOuterPartition
  simp_rw [vectorMeasurePotential_grid_eq_finite μ j β t ht]

theorem vectorMeasureOuterLaw_grid_eq_finite (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t a : ℝ) (ht : t ≤ 1) :
    vectorMeasureOuterLaw (n := n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a =
      vectorOuterLaw (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  unfold vectorMeasureOuterLaw vectorOuterLaw
  rw [vectorMeasureOuterWeight_grid_eq_finite μ j β t a ht]

theorem vectorMeasureDisorderTilt_grid_eq_finite (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t a : ℝ) (ht : t ≤ 1) :
    vectorMeasureDisorderTilt (n := n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a =
      vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  unfold vectorMeasureDisorderTilt vectorFiniteDisorderTilt
  rw [vectorMeasureOuterWeight_grid_eq_finite μ j β t a ht]

theorem vectorMeasureFunctional_grid_eq_finite (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t a : ℝ) (ha : a ≠ 0) (ht : t ≤ 1) :
    vectorMeasureFunctional n (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a =
      finiteVectorFunctional n (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  rw [vectorMeasureFunctional_of_ne n _ β t a ha]
  unfold finiteVectorFunctional
  rw [FRSB.parisiSchemeMeasure_grid_eq]
  simp_rw [vectorMeasurePotential_grid_eq_finite μ j β t ht]

end QuantitativePaper
