module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestTerminalHessian
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileGradientIntegrand

@[expose] public section

/-! Literal native rest response observables, before expectation contraction. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper FRSB
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityZeroRestHessianSquare (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n) : ℝ:=
  Matrix.trace (nativeAnisotropicProcessHessianMatrix D μ p z*
    nativeAnisotropicProcessHessianMatrix D μ p z)/(n:ℝ)^2

def cavityZeroRestMixedHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n) : ℝ:=
  cavitySignedResponseMixedHessian D μ r p z/(n:ℝ)^2

def cavityZeroRestTerminalHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n×Configuration n) : ℝ:=
  (∑i : Fin n,Paper.spinSign (z.2 i)*
    ∑l : Fin n,anisotropicProcessMagnetization D μ p z.1 l*
      nativeAnisotropicProcessHessianMatrix D μ p z.1 l i)/(n:ℝ)^2

def cavityZeroRestFutureFieldDerivative (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (p r : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n) : ℝ:=
  (fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ z.1 p x r)
    (anisotropicMeasureState D μ p z)) (anisotropicProcessMagnetization D μ p z)/(n:ℝ)

end QuantitativeFollowup
