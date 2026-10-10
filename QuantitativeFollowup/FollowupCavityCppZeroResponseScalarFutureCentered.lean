module
public import QuantitativeFollowup.FollowupCavitySignedResponseFutureScalarKernel
public import QuantitativeFollowup.ScalarResponseRootCancellation

@[expose] public section

/-! The actual centered past square paired with a genuine restarted future
square is the source future covariance. The centering constant disappears
by its true zero expectation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem measurable_scalarCenteredSquare_future_extended
    (B : ℝ) (hB : B≠0) (μ : Paper.ParisiMeasure)
    (p r : Paper.Overlap) (hpr : (p:ℝ)≤r) :
    Measurable (fun z : Paper.BrownianSample×Bool=>scalarCenteredSquare B μ p z.1*
      scalarFutureSquareExtended B μ p r (parisiPhysicalSplitState B 0 μ p z.1)):=by
  have hZ:Measurable (scalarCenteredSquare B μ p):=
    ((measurable_M B μ p p.property).pow_const 2).sub measurable_const
  have hG:Measurable (scalarFutureSquareProcess B μ p r hpr):=
    (measurable_scalarFutureSquareProcess_past B hB μ p r hpr).mono
      (canonicalBrownianFiltration.le _) le_rfl
  simpa only [Pi.mul_def,Function.comp_def,scalarFutureSquareProcess,←scalarFutureSquareExtended_eq B μ p r hpr] using
    (hZ.mul hG).comp measurable_fst

theorem norm_scalarCenteredSquare_future_extended_le
    (B : ℝ) (μ : Paper.ParisiMeasure) (p r : Paper.Overlap) (hpr : (p:ℝ)≤r)
    (z : Paper.BrownianSample×Bool) :
    ‖scalarCenteredSquare B μ p z.1*scalarFutureSquareExtended B μ p r
      (parisiPhysicalSplitState B 0 μ p z.1)‖≤1:=by
  rw [scalarFutureSquareExtended_eq B μ p r hpr,norm_mul,
    Real.norm_of_nonneg (scalarFutureSquare_nonneg_le_one B μ p r hpr _).1]
  exact (mul_le_mul (scalarCenteredSquare_norm_le_one B μ p z.1)
    (scalarFutureSquare_nonneg_le_one B μ p r hpr _).2
    (scalarFutureSquare_nonneg_le_one B μ p r hpr _).1 zero_le_one).trans_eq
      (one_mul _)

theorem integral_scalarCenteredSquare_future_eq_covariance
    (B : ℝ) (hB : B≠0) (μ : Paper.ParisiMeasure)
    (p r : Paper.Overlap) (hpr : (p:ℝ)≤r) :
    (∫ω,scalarCenteredSquare B μ p ω*scalarFutureSquareProcess B μ p r hpr ω
      ∂canonicalBrownianMeasure)=cavitySignedScalarFutureCovarianceKernel B μ p r :=by
  let Z:=scalarCenteredSquare B μ p
  let G:=scalarFutureSquareProcess B μ p r hpr
  have hZi:=scalarCenteredSquare_memLp_two B μ p p.property
  have hGi:=scalarFutureSquareProcess_memLp_two B hB μ p r hpr
  have hZG:Integrable (fun ω=>Z ω*G ω) canonicalBrownianMeasure:=hZi.integrable_mul hGi
  have hZC:Integrable (fun ω=>Z ω*Gamma B μ r) canonicalBrownianMeasure:=
    (hZi.integrable one_le_two).mul_const _
  rw [cavitySignedScalarFutureCovarianceKernel_eq_actual_future B hB μ p r hpr]
  unfold covariance
  rw [integral_scalarFutureSquareProcess B hB μ p r hpr]
  change (∫ω,Z ω*G ω ∂canonicalBrownianMeasure)=
    ∫ω,Z ω*(G ω-Gamma B μ r) ∂canonicalBrownianMeasure
  simp_rw [mul_sub]
  rw [integral_sub hZG hZC,integral_mul_const,integral_scalarCenteredSquare,
    zero_mul,sub_zero]

theorem integral_scalarMarked_centered_future_eq_covariance
    (B : ℝ) (hB : B≠0) (μ : Paper.ParisiMeasure)
    (p r : Paper.Overlap) (hpr : (p:ℝ)≤r) :
    (∫z,scalarCenteredSquare B μ p z.1*scalarFutureSquareExtended B μ p r
      (parisiPhysicalSplitState B 0 μ p z.1) ∂scalarMarkedSpinLaw B hB μ)=
      cavitySignedScalarFutureCovarianceKernel B μ p r :=by
  have hZ:Measurable (scalarCenteredSquare B μ p):=
    ((measurable_M B μ p p.property).pow_const 2).sub measurable_const
  have hG:Measurable (scalarFutureSquareProcess B μ p r hpr):=
    (measurable_scalarFutureSquareProcess_past B hB μ p r hpr).mono
      (canonicalBrownianFiltration.le _) le_rfl
  have he:=integral_scalarMarkedSpinLaw_sample B hB μ
    (fun ω=>scalarCenteredSquare B μ p ω*scalarFutureSquareProcess B μ p r hpr ω)
    (hZ.mul hG)
  have h:=he.trans (integral_scalarCenteredSquare_future_eq_covariance B hB μ p r hpr)
  simpa only [Pi.mul_def,Function.comp_def,scalarFutureSquareProcess,←scalarFutureSquareExtended_eq B μ p r hpr] using h

end QuantitativeFollowup
