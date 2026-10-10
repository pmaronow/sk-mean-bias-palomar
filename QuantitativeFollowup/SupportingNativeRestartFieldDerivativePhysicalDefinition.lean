module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMeanScore
public import QuantitativeFollowup.FollowupCavitySignedResponseMixedHessian

@[expose] public section

/-! Literal native initial-field gradient of the future mean-square
observable, contracted with the actual earlier magnetization. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}

def cavitySignedResponseFutureGradient (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (p l : Paper.Overlap) : ℝ :=
  (∫sample,(fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 p x l)
    (anisotropicMeasureState D μ p sample)) (anisotropicProcessMagnetization D μ p sample)
      ∂anisotropicMeasureSampleLaw D μ a)/(n:ℝ)

end QuantitativeFollowup
