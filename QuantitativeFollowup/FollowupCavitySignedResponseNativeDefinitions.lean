module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePhysicalDefinition
public import QuantitativeFollowup.FollowupCavitySignedResponseT2Original
public import QuantitativeFollowup.FollowupCavitySignedResponseT3LastHessian
public import QuantitativeFollowup.FollowupCavitySignedResponseDiagonalIntegral

@[expose] public section

/-! Literal original Tp: T1 and T2 use actual centered rest observables,
and T3 uses the true native initial-field derivative of the restarted
future self-overlap. No response identity or estimate is an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
variable {n : ℕ}

def cavitySignedResponseT2 (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (hβ0 : β0≠0) (p : Paper.Overlap) : ℝ :=
  cavitySignedResponseT2First D μ a β0 hβ0 p+cavitySignedResponseT2Double D μ a β0 p

def cavitySignedResponseT3 (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (p : Paper.Overlap) : ℝ :=
  cavitySignedResponseT3Diagonal D μ a β0 p-
    (∫l,cavitySignedScalarStrictFutureKernel β0 μ p l*cavitySignedResponseFutureGradient D μ a p l
      ∂parisiFreeMeasure μ a)-cavitySignedResponseT3LastHessian D μ a β0 p

def cavitySignedResponseT (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (hβ0 : β0≠0) (p : Paper.Overlap) : ℝ :=
  cavitySignedResponseT1 D μ a β0 hβ0 p+cavitySignedResponseT2 D μ a β0 hβ0 p+
    cavitySignedResponseT3 D μ a β0 p

end QuantitativeFollowup
