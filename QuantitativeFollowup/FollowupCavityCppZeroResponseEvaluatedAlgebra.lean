module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseSevenKernels
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeDefinitions

@[expose] public section

/-! Pure exact algebra of the evaluated last/rest/density contributions.
The profile, covariance-column placeholder and three residual values are
arbitrary. No expectation or physical-response premise is used. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper Paper FRSB
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 900000

def cavityEvaluatedSevenExpression (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ)
    (φ : Paper.Overlap→ℝ) (p : Paper.Overlap) (Theta : ℝ) : ℝ :=
  (scalarResponseKernel0 β μ p 0 0+
      2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0)*φ p
    -(∫r in Ioi p,scalarResponseKernel2 β μ p r 0*φ r∂parisiFreeMeasure μ a)
    -2*(∫r,scalarResponseKernel3 β μ p r 0*φ (min p r)∂parisiFreeMeasure μ a)
    -(∫r,scalarResponseKernel4 β μ p r 0*φ r∂parisiFreeMeasure μ a)
    +(1/2:ℝ)*(∫r,parisiCDF μ r*scalarResponseKernel5 β μ p r r*φ r∂parisiFreeMeasure μ a)
    +(1/2:ℝ)*(∫r,∫l,scalarResponseKernel6 β μ p r l*φ (min r l)
        ∂parisiFreeMeasure μ a∂parisiFreeMeasure μ a)
    +(1/2:ℝ)*Theta

theorem cavityZeroResponse_evaluated_algebra
    (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (φ : Paper.Overlap→ℝ)
    (p : Paper.Overlap) (Theta T1 T2 T3 : ℝ) :
    ((scalarResponseKernel0 β μ p p 0+
        2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0)*φ p-
      (∫r,if p<r then φ r*scalarResponseKernel2 β μ p r 0 else 0∂parisiFreeMeasure μ a)-
      2*(∫r,φ (min p r)*scalarResponseKernel3 β μ p r 0∂parisiFreeMeasure μ a)+T1)+
    (-(∫r,φ r*scalarResponseKernel4 β μ p r 0∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,∫l,φ (min r l)*scalarResponseKernel6 β μ p r l
        ∂parisiFreeMeasure μ a∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,parisiCDF μ r*(φ r*scalarResponseKernel5 β μ p r r)∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*Theta+T2)+T3=
      cavityEvaluatedSevenExpression β μ a φ p Theta+(T1+T2+T3) := by
  have h0 : scalarResponseKernel0 β μ p p 0=scalarResponseKernel0 β μ p 0 0 := rfl
  have h2 : (∫r,if p<r then φ r*scalarResponseKernel2 β μ p r 0 else 0∂parisiFreeMeasure μ a)=
      ∫r in Ioi p,scalarResponseKernel2 β μ p r 0*φ r∂parisiFreeMeasure μ a := by
    have he : (fun r : Paper.Overlap=>if p<r then φ r*scalarResponseKernel2 β μ p r 0 else 0)=
        (Ioi p).indicator (fun r=>scalarResponseKernel2 β μ p r 0*φ r) := by
      funext r
      simp only [Set.indicator_apply,mem_Ioi]
      split_ifs <;> ring
    rw [he,integral_indicator measurableSet_Ioi]
  have h3 : (∫r,φ (min p r)*scalarResponseKernel3 β μ p r 0∂parisiFreeMeasure μ a)=
      ∫r,scalarResponseKernel3 β μ p r 0*φ (min p r)∂parisiFreeMeasure μ a :=
    integral_congr_ae (.of_forall fun _=>mul_comm _ _)
  have h4 : (∫r,φ r*scalarResponseKernel4 β μ p r 0∂parisiFreeMeasure μ a)=
      ∫r,scalarResponseKernel4 β μ p r 0*φ r∂parisiFreeMeasure μ a :=
    integral_congr_ae (.of_forall fun _=>mul_comm _ _)
  have h5 : (∫r,parisiCDF μ r*(φ r*scalarResponseKernel5 β μ p r r)∂parisiFreeMeasure μ a)=
      ∫r,parisiCDF μ r*scalarResponseKernel5 β μ p r r*φ r∂parisiFreeMeasure μ a :=
    integral_congr_ae (.of_forall fun _=>by ring)
  have h6 : (∫r,∫l,φ (min r l)*scalarResponseKernel6 β μ p r l
      ∂parisiFreeMeasure μ a∂parisiFreeMeasure μ a)=
      ∫r,∫l,scalarResponseKernel6 β μ p r l*φ (min r l)
        ∂parisiFreeMeasure μ a∂parisiFreeMeasure μ a := by
    apply integral_congr_ae
    exact .of_forall fun _=>integral_congr_ae (.of_forall fun _=>mul_comm _ _)
  rw [h0,h2,h3,h4,h5,h6]
  unfold cavityEvaluatedSevenExpression
  ring

theorem cavityZeroResponse_evaluated_native_algebra {n : ℕ}
    (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    let φ := cavityRestCovarianceColumn D μ a p
    ((scalarResponseKernel0 β μ p p 0+
        2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0)*φ p-
      (∫r,if p<r then φ r*scalarResponseKernel2 β μ p r 0 else 0∂parisiFreeMeasure μ a)-
      2*(∫r,φ (min p r)*scalarResponseKernel3 β μ p r 0∂parisiFreeMeasure μ a)+
      cavitySignedResponseT1 D μ a β hβ p)+
    (-(∫r,φ r*scalarResponseKernel4 β μ p r 0∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,∫l,φ (min r l)*scalarResponseKernel6 β μ p r l
        ∂parisiFreeMeasure μ a∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,parisiCDF μ r*(φ r*scalarResponseKernel5 β μ p r r)∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*cavityScalarRestThetaLast D β μ a p+cavitySignedResponseT2 D μ a β hβ p)+
      cavitySignedResponseT3 D μ a β p=
      cavityScalarRestModifiedSeven D β μ a p+cavitySignedResponseT D μ a β hβ p := by
  dsimp only
  have h := cavityZeroResponse_evaluated_algebra β μ a (cavityRestCovarianceColumn D μ a p) p
    (cavityScalarRestThetaLast D β μ a p) (cavitySignedResponseT1 D μ a β hβ p)
    (cavitySignedResponseT2 D μ a β hβ p) (cavitySignedResponseT3 D μ a β p)
  exact h

end QuantitativeFollowup
