module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseKernelContraction

@[expose] public section

/-! The literal six scalar response terms and the actual conditional seventh
term contract to the covariance-column response plus half of the genuine
future remainder. This algebra does not assert the physical Cpp derivative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def cavityScalarRestModifiedSeven (D : AnisotropicSpinModel n) (β : ℝ)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) : ℝ :=
  let φ := cavityRestCovarianceColumn D μ a p
  (scalarResponseKernel0 β μ p 0 0+
      2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0)*φ p
    -(∫r in Ioi p,scalarResponseKernel2 β μ p r 0*φ r ∂parisiFreeMeasure μ a)
    -2*(∫r,scalarResponseKernel3 β μ p r 0*φ (min p r) ∂parisiFreeMeasure μ a)
    -(∫r,scalarResponseKernel4 β μ p r 0*φ r ∂parisiFreeMeasure μ a)
    +(1/2:ℝ)*(∫r,parisiCDF μ r*scalarResponseKernel5 β μ p r r*φ r
        ∂parisiFreeMeasure μ a)
    +(1/2:ℝ)*(∫r,∫l,scalarResponseKernel6 β μ p r l*φ (min r l)
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)
    +(1/2:ℝ)*cavityScalarRestThetaLast D β μ a p

theorem cavityScalarRestModifiedSeven_eq_response_add_half_remainder
    (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    β^2*cavityScalarRestModifiedSeven D β μ a p=
      scalarResponseOperator β hβ μ a (cavityRestCovarianceColumn D μ a p) p+
        (β^2/2)*cavityResponseFutureRemainder β D μ a p := by
  have hlast :
      (∫r,∫l in Ioi r,scalarFutureCenteredPairing β μ p r l*
          cavityRestCovarianceColumn D μ a p l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=
        ∫r,∫l in Ioi r,scalarResponseKernel7 β μ p r l*
          cavityRestCovarianceColumn D μ a p l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a := by
    apply integral_congr_ae
    exact .of_forall fun r=>by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro l hl
      dsimp only
      rw [scalarFutureCenteredPairing_eq_kernel β μ p r l hl.le]
  have htheta:=cavityScalarRestThetaLast_eq_covariance_column_add_remainder D β hβ μ a p
  rw [hlast] at htheta
  rw [scalarResponseOperator_eq_kernels]
  dsimp only [cavityScalarRestModifiedSeven]
  rw [htheta]
  ring

theorem integrable_cavityScalarRestModifiedSeven_scaled
    (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    Integrable (fun p=>β^2*cavityScalarRestModifiedSeven D β μ a p)
      (parisiFreeMeasure μ a) := by
  have hi:=(integrable_cavityRestResponseTrace_kernel_diagonal D β hβ μ a ha hμ).add
    ((integrable_cavityResponseFutureRemainder β hβ D μ a).const_mul (β^2/2))
  exact hi.congr (.of_forall fun p=>
    (cavityScalarRestModifiedSeven_eq_response_add_half_remainder D β hβ μ a p).symm)

theorem cavityScalarRestModifiedSeven_integral_eq_trace_sub_half_penalty
    (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    (∫p,β^2*cavityScalarRestModifiedSeven D β μ a p ∂parisiFreeMeasure μ a)=
      cavityRestResponseTrace D β hβ μ a ha hμ-(β^2/2)*cavityResidualPenalty β D μ a := by
  simp_rw [cavityScalarRestModifiedSeven_eq_response_add_half_remainder D β hβ μ a]
  rw [integral_add (integrable_cavityRestResponseTrace_kernel_diagonal D β hβ μ a ha hμ)
      ((integrable_cavityResponseFutureRemainder β hβ D μ a).const_mul (β^2/2)),
    integral_const_mul,
    ←cavityRestResponseTrace_eq_kernel_diagonal D β hβ μ a ha hμ hone,
    cavityResponseFutureRemainder_integral_eq_neg_penalty β hβ D μ a]
  ring

end QuantitativeFollowup
