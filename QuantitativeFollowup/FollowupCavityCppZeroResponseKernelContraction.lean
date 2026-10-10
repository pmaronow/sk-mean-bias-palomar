module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarKernel
public import QuantitativeFollowup.FollowupCavityRemainderIntegral
public import QuantitativeFollowup.FollowupCavityRestTraceDiagonal
public import QuantitativeFollowup.ScalarResponseNormBounds

@[expose] public section

/-! Exact contraction of the actual scalar/rest seven response kernels.
Only the last term changes from a covariance column to its true conditional
projection. Its difference is the literal future remainder, without a
covariance-response conclusion supplied as a hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityScalarRestThetaLast (D : AnisotropicSpinModel n) (β : ℝ)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) : ℝ :=
  ∫r,∫l in Ioi r,scalarFutureCenteredPairing β μ p r l*
    cavityRestProjectedCovariance D μ a r l p ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a

private theorem sigma_last_integrable (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Integrable (fun z : Paper.Overlap×Paper.Overlap=>
      if z.1<z.2 then scalarResponseKernel7 β μ p z.1 z.2*
        cavityRestCovarianceColumn D μ a p z.2 else 0)
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) :=by
  let φ:=cavityRestCovarianceColumn D μ a p
  have harg : Continuous (fun z : Paper.Overlap×Paper.Overlap=>(μ,(p,(z.1,z.2))) :
      Paper.Overlap×Paper.Overlap→ScalarResponseKernelParameters) :=by fun_prop
  have hm : Measurable (fun z : Paper.Overlap×Paper.Overlap=>
      if z.1<z.2 then scalarResponseKernel7 β μ p z.1 z.2*φ z.2 else 0) :=
    (((continuous_scalarResponseKernel7 β hβ).comp harg).mul
      (φ.continuous.comp continuous_snd)).measurable.ite
        (measurableSet_lt measurable_fst measurable_snd) measurable_const
  apply (integrable_const (scalarResponseKernelBound β*‖φ‖)).mono' hm.aestronglyMeasurable
  exact .of_forall fun z=>by
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (scalarResponseKernel_bounds β μ p z.1 z.2).2.2.2.2.2.2.2
        (φ.norm_coe_le_norm z.2) (norm_nonneg _) (by linarith [scalarResponseKernelBound_ge_one β])
    · simp only [norm_zero]
      exact mul_nonneg (zero_le_one.trans (scalarResponseKernelBound_ge_one β)) (norm_nonneg φ)

private theorem residual_last_integrable (D : AnisotropicSpinModel n) (β : ℝ)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Integrable (fun z : Paper.Overlap×Paper.Overlap=>
      cavityScalarFutureCovariance β μ z.1 p z.2*cavityRestResidualCovariance D μ a z.1 p z.2)
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) :=by
  have hmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)=>(z.1,(p,z.2))) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have hm:=((measurable_cavityScalarFutureCovariance β μ).comp hmap).mul
    ((measurable_cavityRestResidualCovariance D μ a).comp hmap)
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  exact .of_forall fun z=>by
    change ‖cavityScalarFutureCovariance β μ z.1 p z.2*
      cavityRestResidualCovariance D μ a z.1 p z.2‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (cavityScalarFutureCovariance_norm_le β μ _ _ _)
      (cavityRestResidualCovariance_norm_le D μ a _ _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem cavityScalarRestThetaLast_eq_covariance_column_add_remainder
    (D : AnisotropicSpinModel n) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    cavityScalarRestThetaLast D β μ a p=
      (∫r,∫l in Ioi r,scalarFutureCenteredPairing β μ p r l*
        cavityRestCovarianceColumn D μ a p l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
      cavityResponseFutureRemainder β D μ a p :=by
  let ν:=parisiFreeMeasure μ a
  let F:=fun z : Paper.Overlap×Paper.Overlap=>if z.1<z.2 then
    scalarResponseKernel7 β μ p z.1 z.2*cavityRestCovarianceColumn D μ a p z.2 else 0
  let R:=fun z : Paper.Overlap×Paper.Overlap=>
    cavityScalarFutureCovariance β μ z.1 p z.2*cavityRestResidualCovariance D μ a z.1 p z.2
  have hiF : Integrable F (ν.prod ν):=sigma_last_integrable D β hβ μ a p
  have hiR : Integrable R (ν.prod ν):=residual_last_integrable D β μ a p
  have he (r l : Paper.Overlap) :
      (if r<l then scalarFutureCenteredPairing β μ p r l*
        cavityRestProjectedCovariance D μ a r l p else 0)=F (r,l)-R (r,l) :=by
    by_cases hl : r<l
    · rw [if_pos hl]
      dsimp only [F,R]
      rw [if_pos hl,scalarFutureCenteredPairing_eq_projectedCovariance β μ p r l hl.le,
        scalarResponseKernel7_eq_projectedCovariance β μ p r l hl.le,
        cavityRestCovarianceColumn_eq_covariance,
        covariance_comm (cavityRestSelfOverlap D μ p) (cavityRestSelfOverlap D μ l)]
      have hh:=cavityProjectedCovariance_product_eq_residual D β hβ μ a r p l hl
      linear_combination hh
    · rw [if_neg hl]
      dsimp only [F,R]
      rw [if_neg hl,cavityScalarFutureCovariance_eq_mask]
      simp [hl]
  have hSigma (r : Paper.Overlap) :
      (∫l in Ioi r,scalarFutureCenteredPairing β μ p r l*cavityRestCovarianceColumn D μ a p l ∂ν)=
        ∫l,F (r,l) ∂ν :=by
    rw [←integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact .of_forall fun l=>by
      by_cases hl : r<l
      · rw [indicator_of_mem (show l∈(Ioi r : Set Paper.Overlap) from hl)]
        dsimp only [F]
        rw [if_pos hl,scalarFutureCenteredPairing_eq_kernel β μ p r l hl.le]
      · rw [indicator_of_notMem (show l∉(Ioi r : Set Paper.Overlap) from hl)]
        simp [F,hl]
  have hTheta (r : Paper.Overlap) :
      (∫l in Ioi r,scalarFutureCenteredPairing β μ p r l*cavityRestProjectedCovariance D μ a r l p ∂ν)=
        ∫l,F (r,l)-R (r,l) ∂ν :=by
    rw [←integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact .of_forall fun l=>by
      simpa only [indicator_apply,mem_Ioi] using he r l
  have hiRF : Integrable (fun r=>∫l,R (r,l) ∂ν) ν:=hiR.integral_prod_left
  have hiFF : Integrable (fun r=>∫l,F (r,l) ∂ν) ν:=hiF.integral_prod_left
  have hsplit : (∫r,∫l,F (r,l)-R (r,l) ∂ν ∂ν)=
      (∫r,∫l,F (r,l) ∂ν ∂ν)-(∫r,∫l,R (r,l) ∂ν ∂ν) :=by
    rw [←integral_sub hiFF hiRF]
    apply integral_congr_ae
    filter_upwards [hiF.prod_right_ae,hiR.prod_right_ae] with r hF hR
    exact integral_sub hF hR
  have htotalTheta : cavityScalarRestThetaLast D β μ a p=
      ∫r,∫l,F (r,l)-R (r,l) ∂ν ∂ν := by
    unfold cavityScalarRestThetaLast
    apply integral_congr_ae
    exact .of_forall hTheta
  have htotalSigma :
      (∫r,∫l in Ioi r,scalarFutureCenteredPairing β μ p r l*
        cavityRestCovarianceColumn D μ a p l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=
      ∫r,∫l,F (r,l) ∂ν ∂ν := by
    apply integral_congr_ae
    exact .of_forall hSigma
  rw [htotalTheta,hsplit,htotalSigma,
    cavityResponseFutureRemainder_eq_residual_integral β hβ D μ a p]
  dsimp only [R,ν]
  ring

end QuantitativeFollowup
