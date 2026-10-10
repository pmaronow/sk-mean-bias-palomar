module
public import QuantitativeFollowup.FourTermBudgetTrial
public import QuantitativeFollowup.SmallIntervalDecomposition

@[expose] public section

/-! The complete printed optimized-density identities in energy units.
The individual A,J,V belong to any genuine attaining profile; their sum
is independent of that choice at minimum differentiability points. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1900000

theorem smallIntervalDefect_printed_derivative (n : ℕ) (β lam rho : ℝ)
    (hβ : β ≠ 0) :
    smallIntervalDefect n β lam rho =
      -4/β*deriv (vectorInterpolationMinimum n β (lam/β)) (1-rho) := by
  unfold smallIntervalDefect optimizedVectorInterpolationDefect
  field_simp [hβ]
  <;> ring

theorem smallIntervalDefect_printed_decomposition (n : ℕ) (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β lam rho : ℝ) (hβ : 0<β)
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hs : lam/β ∈ Ioo (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor (lam/β))
    (hmin : ∀ν ∈ scalarFloor (lam/β),vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤
      vectorMeasureFunctional n ν β (1-rho) (lam/β))
    (hf : DifferentiableAt ℝ (vectorInterpolationMinimum n β (lam/β)) (1-rho)) :
    smallIntervalDefect n β lam rho = β *
      (vectorInterpolationTraceError (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1]) +
       2*vectorMeanDirectionCovarianceIntegral (n:=n) μ (lam/β) β (1-rho) (lam/β)
         (by linarith [hrho.1]) +
       vectorIntegratedSelfOverlapVariance (n:=n) μ (lam/β) β (1-rho)
         (by linarith [hrho.1])) := by
  unfold smallIntervalDefect
  rw [optimizedVectorInterpolationDefect_eq_of_minimizer hn μ β (lam/β) hs hμ hβ.ne'
    (1-rho) ⟨by linarith [hrho.2],by linarith [hrho.1]⟩ hmin hf,
    smallInterval_defect_decomposition hn μ (lam/β) β (1-rho) hβ.ne'
      (by linarith [hrho.1]) hs hμ hmin]

theorem smallIntervalDefect_printed_envelope (n : ℕ) (hn : 0<n)
    (β lam : ℝ) (hβ : 0<β) (hs : lam/β ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (smallIntervalDefect n β lam) volume 0 1 ∧
    4*energyComparisonError n β lam = ∫rho in (0 : ℝ)..1,smallIntervalDefect n β lam rho :=
  fourTermBudget_native_envelope n hn β lam hβ hs

end QuantitativeFollowup
