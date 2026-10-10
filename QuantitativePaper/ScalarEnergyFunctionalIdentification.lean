module
public import QuantitativePaper.ResponseFunctional
public import QuantitativePaper.EnergyMomentIdentity
public import FRSB.ParisiMinimizerGeometry

@[expose] public section

/-! The literal scalar energy functional is the zero-time vector endpoint.
The identification holds for every positive dimension and every tilt. -/
noncomputable section
open Set MeasureTheory Paper
namespace QuantitativePaper

theorem responseEnergyFunctional_zero (n : ℕ) (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β lam : ℝ) (hβ : β≠0) :
    responseEnergyFunctional n μ β 0 lam=scalarParisiFunctional β μ/β := by
  rw [responseEnergyFunctional,vectorMeasureFunctional_zero n hn μ β hβ]

theorem scalarEnergyValue_zero_of_minimizer (β : ℝ) (μ : Paper.ParisiMeasure)
    (hμ : FRSB.IsParisiMinimizer β 0 μ) :
    scalarEnergyValue β 0=scalarParisiFunctional β μ/β := by
  rw [scalarEnergyValue,zero_div,constrainedParisiValue_zero]
  rw [←(FRSB.isParisiMinimizer_iff_infimum β 0 μ).mp hμ]
  rfl

theorem responseEnergyFunctional_zero_of_minimizer (n : ℕ) (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β lam : ℝ) (hβ : β≠0)
    (hμ : FRSB.IsParisiMinimizer β 0 μ) :
    responseEnergyFunctional n μ β 0 lam=scalarEnergyValue β 0 := by
  rw [responseEnergyFunctional_zero n hn μ β lam hβ,
    scalarEnergyValue_zero_of_minimizer β μ hμ]

end QuantitativePaper
