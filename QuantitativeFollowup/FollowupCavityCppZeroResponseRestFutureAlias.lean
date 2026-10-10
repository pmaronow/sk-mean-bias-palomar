module
public import QuantitativeFollowup.FollowupCavityRestFutureSquare
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMeanSquare

@[expose] public section

/-! The actual rest future square is the deterministic-field native restart
mean square evaluated at the original process state. This is pointwise,
including equal times and zero-dimensional normalization; no conditional
expectation representative is differentiated. -/
noncomputable section
open MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
set_option autoImplicit false
variable {n : ℕ}
set_option maxHeartbeats 1000000

 theorem cavityRestFutureSquare_eq_restartMeanSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q ≤ r)
    (sample : AnisotropicDisorderBrownianSample n) :
    cavityRestFutureSquare D μ q r sample =
      anisotropicRestartMeanSquare D μ sample.1 q
        (anisotropicMeasureState D μ q sample) r := by
  rw [cavityRestFutureSquare_eq_conditional_square D μ q r hqr sample]
  unfold anisotropicRestartMeanSquare
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    anisotropicRestartConditionalSpinSquare_eq_restart D μ q r hqr i sample

 theorem cavityRestFutureSquare_eq_restartMeanSquare_function (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q ≤ r) :
    cavityRestFutureSquare D μ q r = fun sample =>
      anisotropicRestartMeanSquare D μ sample.1 q
        (anisotropicMeasureState D μ q sample) r :=
  funext fun sample => cavityRestFutureSquare_eq_restartMeanSquare D μ q r hqr sample

end QuantitativeFollowup
