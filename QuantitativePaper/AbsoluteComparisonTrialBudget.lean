module
public import QuantitativePaper.InterpolationEnvelope
public import QuantitativePaper.ScalarEnergyFunctionalIdentification
public import QuantitativePaper.GroundQuantitativePassage

@[expose] public section

/-! The actual fixed-profile trial budget follows from the two physical
interpolation endpoints and the genuine scalar clipping cost. -/
noncomputable section
open Set MeasureTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 1200000
variable {n : ℕ}

theorem absolute_trial_budget (hn : 0<n) (μ ν : ParisiMeasure)
    (β lam t C1 : ℝ) (hβ : 0<β) (hs : lam/β∈Ioo (0:ℝ) 1)
    (ht : t∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor (lam/β)) (hν : ν∈scalarFloor (lam/β))
    (hmin : ∀ρ∈scalarFloor (lam/β), vectorMeasureFunctional n μ β t (lam/β) ≤ 
      vectorMeasureFunctional n ρ β t (lam/β))
    (hzero : 0 ≤ scalarEnergyValue β lam-scalarEnergyValue β 0)
    (hcost : parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0 ≤ C1*lam^5) :
    responseEnergyFunctional n ν β t lam-responseEnergyFunctional n μ β t lam ≤ 
      energyComparisonError n β lam+C1*lam^5 := by
  have hup:=vectorMeasureFunctional_interpolation_antitone hn ν β (lam/β) hs hν hβ.ne'
    (by norm_num : (0:ℝ)∈Icc 0 1) ht ht.1
  have hlo:=vectorInterpolationMinimum_antitone n hn β (lam/β) hs hβ.ne'
    ht (by norm_num : (1:ℝ)∈Icc 0 1) ht.2
  rw [←vectorInterpolationMinimum_eq_of_minimizer hn μ β (lam/β) t hs.2.le ht.2 hμ hmin,
    vectorInterpolationMinimum_one n β (lam/β) hs.2.le hs.1.ne'] at hlo
  have hbudget:=div_le_div_of_nonneg_right (sub_le_sub hup hlo) hβ.le
  change responseEnergyFunctional n ν β t lam-responseEnergyFunctional n μ β t lam ≤ _ 
  rw [energyComparisonError_eq_fractional_gap n β lam hβ.ne',sub_div]
  have heq : (vectorMeasureFunctional n ν β t (lam/β)-vectorMeasureFunctional n μ β t (lam/β))/β=
      responseEnergyFunctional n ν β t lam-responseEnergyFunctional n μ β t lam := by
    unfold responseEnergyFunctional
    ring
  rw [heq] at hbudget
  change parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0 ≤ C1*lam^5 at hcost
  have hend : (vectorMeasureFunctional n ν β 0 (lam/β)-completedFractionalPressure n β (lam/β))/β=
      parisiPDEFunctional β 0 ν/β-completedFractionalPressure n β (lam/β)/β := by
    rw [vectorMeasureFunctional_zero n hn ν β hβ.ne']
    unfold scalarParisiFunctional
    ring
  rw [hend] at hbudget
  change 0 ≤ constrainedParisiValue β (lam/β)/β-scalarEnergyValue β 0 at hzero
  linarith

end QuantitativePaper
