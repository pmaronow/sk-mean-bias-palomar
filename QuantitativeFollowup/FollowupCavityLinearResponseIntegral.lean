module
public import QuantitativeFollowup.FollowupCavityTraceCovarianceData
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeEstimate

@[expose] public section

/-! Genuine integrability and exact integration of the source's constructed
diagonal-linear right-hand side. This does not identify it with Cpp′. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem integrable_cavitySignedResponseT_native (D : AnisotropicSpinModel n) (hn : 0<n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    Integrable (cavitySignedResponseT D μ a β0 hβ0) (parisiFreeMeasure μ a):=by
  have h1:=integrable_cavitySignedResponseT1 D μ a β0 hβ0
  have h2:=(integrable_cavitySignedResponseT2First D μ a β0 hβ0).add
    (integrable_cavitySignedResponseT2Double D μ a β0 hβ0)
  have h3:=(((integrable_cavitySignedResponseT3Diagonal D μ a β0 hβ0).sub
    (integrable_cavitySignedResponseT3Explicit D μ a β0 hβ0)).sub
    (integrable_cavitySignedResponseT3Score D μ a β0 hβ0 ha)).sub
    (integrable_cavitySignedResponseT3LastHessian D μ a β0 hβ0)
  have h3native : Integrable (cavitySignedResponseT3 D μ a β0) (parisiFreeMeasure μ a):=
    h3.congr (.of_forall fun p=>(cavitySignedResponseT3_eq_native_score_decomposition
      D hn μ a β0 hβ0 ha hμ p).symm)
  exact (h1.add h2).add h3native

 def followupCavityLinearResponseRightSide (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) : ℝ:=
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let β0:=followupCavityScalarBeta n β ρ
  let hb:= (followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
  followupCavityAlpha n β ρ*
    ((1/followupCavityD n β ρ)*scalarResponseOperator β0 hb μ a
      (cavityRestCovarianceColumn D μ a p) p+
      cavitySignedResponseT D μ a β0 hb p+(1/2)*cavityResponseFutureRemainder β0 D μ a p)

 theorem integrable_followupCavityLinearResponseRightSide (n : ℕ) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    Integrable (followupCavityLinearResponseRightSide n β ρ hβ hρ μ a)
      (parisiFreeMeasure μ a):=by
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let β0:=followupCavityScalarBeta n β ρ
  have hb : β0≠0:=(followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
  have hi:=(integrable_cavityRestResponseTrace_kernel_diagonal D β0 hb μ a ha hμ).const_mul
    (1/followupCavityD n β ρ)
  have hT:=integrable_cavitySignedResponseT_native D hn μ a β0 hb ha hμ
  have hR:=(integrable_cavityResponseFutureRemainder β0 hb D μ a).const_mul (1/2:ℝ)
  exact ((hi.add hT).add hR).const_mul (followupCavityAlpha n β ρ)

 theorem followupCavityLinearResponseRightSide_integral (n : ℕ) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    (∫p,followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p∂parisiFreeMeasure μ a)=
      followupCavityAlpha n β ρ*
        ((1/followupCavityD n β ρ)*followupCavityTraceMinus n β ρ hβ hρ μ a ha hμ-
          followupCavityPenalty n β ρ hβ hρ μ a/2+
          ∫p,cavitySignedResponseT (followupCavityRestSpinModel n β ρ hβ hρ) μ a
            (followupCavityScalarBeta n β ρ) (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p
            ∂parisiFreeMeasure μ a):=by
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let β0:=followupCavityScalarBeta n β ρ
  have hb : β0≠0:=(followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
  have hi:=(integrable_cavityRestResponseTrace_kernel_diagonal D β0 hb μ a ha hμ).const_mul
    (1/followupCavityD n β ρ)
  have hT:=integrable_cavitySignedResponseT_native D hn μ a β0 hb ha hμ
  have hR:=(integrable_cavityResponseFutureRemainder β0 hb D μ a).const_mul (1/2:ℝ)
  unfold followupCavityLinearResponseRightSide
  change (∫p,followupCavityAlpha n β ρ*
    ((1/followupCavityD n β ρ)*scalarResponseOperator β0 hb μ a
      (cavityRestCovarianceColumn D μ a p) p+cavitySignedResponseT D μ a β0 hb p+
        (1/2)*cavityResponseFutureRemainder β0 D μ a p)∂parisiFreeMeasure μ a)=_
  rw [integral_const_mul,
    integral_add (f:=fun p=>(1/followupCavityD n β ρ)*scalarResponseOperator β0 hb μ a
      (cavityRestCovarianceColumn D μ a p) p+cavitySignedResponseT D μ a β0 hb p)
      (g:=fun p=>(1/2)*cavityResponseFutureRemainder β0 D μ a p) (hi.add hT) hR,
    integral_add (f:=fun p=>(1/followupCavityD n β ρ)*scalarResponseOperator β0 hb μ a
      (cavityRestCovarianceColumn D μ a p) p) (g:=cavitySignedResponseT D μ a β0 hb) hi hT,
    integral_const_mul,integral_const_mul,
    ←cavityRestResponseTrace_eq_kernel_diagonal D β0 hb μ a ha hμ hone,
    cavityResponseFutureRemainder_integral_eq_neg_penalty β0 hb D μ a]
  change followupCavityAlpha n β ρ*
    ((1/followupCavityD n β ρ)*followupCavityTraceMinus n β ρ hβ hρ μ a ha hμ+
      (∫p,cavitySignedResponseT D μ a β0 hb p∂parisiFreeMeasure μ a)+
      (1/2)*(-followupCavityPenalty n β ρ hβ hρ μ a))=_
  ring

end QuantitativeFollowup
