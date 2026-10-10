module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestObservables
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments
public import QuantitativeFollowup.ScalarResponseSamples
public import QuantitativeFollowup.ScalarResponseRootCancellation
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeDefinitions

@[expose] public section

/-! The literal six-term native rest integrand, separated from its expectation proof. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityZeroRestResponseIntegrand (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) : ℝ:=
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let xr:=(cavityZeroMarkedSampleSplit n z).1
  let xs:=(cavityZeroMarkedSampleSplit n z).2
  cavityZeroRestHessianSquare D μ p xr.1*scalarResponseSample 5 B μ p p 0 xs+
    4*(cavityZeroRestMixedHessian D μ p p xr.1*scalarResponseSample 1 B μ p 0 0 xs)-
    2*Paper.parisiCDF μ p*(cavityZeroRestMixedHessian D μ p p xr.1*scalarResponseSample 5 B μ p p 0 xs)+
    2*(cavityZeroRestTerminalHessian D μ p xr*
      (scalarCenteredSquare B μ p xs.1*M B μ p xs.1*Paper.spinSign xs.2))-
    (∫r,if p<r then cavityZeroRestFutureFieldDerivative D μ p r xr.1*
      (scalarCenteredSquare B μ p xs.1*scalarFutureSquareExtended B μ p r
        (parisiPhysicalSplitState B 0 μ p xs.1)) else 0 ∂parisiFreeMeasure μ a)-
    2*(∫r,cavityZeroRestMixedHessian D μ r p xr.1*scalarResponseSample 6 B μ p p r xs
      ∂parisiFreeMeasure μ a)

end QuantitativeFollowup
