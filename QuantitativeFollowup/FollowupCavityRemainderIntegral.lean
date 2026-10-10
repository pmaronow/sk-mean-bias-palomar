module
public import QuantitativeFollowup.FollowupCavityScalarCovarianceReduction

@[expose] public section

/-! The literal source future-covariance remainder integrates to minus
its genuine nonnegative product-space square penalty. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def cavityResponseFutureRemainder (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) : ℝ:=
  ∫r,∫l in Ioi r,cavityScalarProjectedCovariance β μ p r l*
    (cavityRestProjectedCovariance D μ a r l p-
      covariance (cavityRestSelfOverlap D μ l) (cavityRestSelfOverlap D μ p)
        (anisotropicMeasureSampleLaw D μ a)) ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a

 theorem cavityResponseFutureRemainder_eq_residual_integral (β : ℝ) (hβ : β≠0)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    cavityResponseFutureRemainder β D μ a p=
      -(∫r,∫l,cavityScalarFutureCovariance β μ r p l*cavityRestResidualCovariance D μ a r p l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a) := by
  have hs (r : Paper.Overlap) :
      (∫l in Ioi r,cavityScalarFutureCovariance β μ r p l*cavityRestResidualCovariance D μ a r p l
        ∂parisiFreeMeasure μ a)=
      ∫l,cavityScalarFutureCovariance β μ r p l*cavityRestResidualCovariance D μ a r p l
        ∂parisiFreeMeasure μ a:=by
    rw [←integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact .of_forall fun l=>by
      by_cases hl : r<l
      · rw [indicator_of_mem (show l∈(Ioi r : Set Paper.Overlap) from hl)]
      · rw [indicator_of_notMem (show l∉(Ioi r : Set Paper.Overlap) from hl)]
        simp [cavityScalarFutureCovariance_eq_mask,hl]
  calc
    _=∫r,∫l in Ioi r,-(cavityScalarFutureCovariance β μ r p l*
        cavityRestResidualCovariance D μ a r p l)
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a:=by
      apply integral_congr_ae
      exact .of_forall fun r=>by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
        exact cavityProjectedCovariance_product_eq_residual D β hβ μ a r p l hl
    _=-(∫r,∫l,cavityScalarFutureCovariance β μ r p l*cavityRestResidualCovariance D μ a r p l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a):=by
      simp_rw [integral_neg,hs]

 theorem integrable_cavityResidualKernel_double (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Integrable (fun z : Paper.Overlap×Paper.Overlap=>∫l,
      cavityScalarFutureCovariance β μ z.2 z.1 l*cavityRestResidualCovariance D μ a z.2 z.1 l
        ∂parisiFreeMeasure μ a) ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) := by
  have hmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×Paper.Overlap=>
      (z.1.2,(z.1.1,z.2))):=by fun_prop
  have hm:=((measurable_cavityScalarFutureCovariance β μ).comp hmap).mul
    ((measurable_cavityRestResidualCovariance D μ a).comp hmap)
  have hmeas : Measurable (fun z : Paper.Overlap×Paper.Overlap=>∫l,
      cavityScalarFutureCovariance β μ z.2 z.1 l*cavityRestResidualCovariance D μ a z.2 z.1 l
        ∂parisiFreeMeasure μ a):=hm.stronglyMeasurable.integral_prod_right'.measurable
  apply (integrable_const ((parisiFreeMeasure μ a).real univ)).mono' hmeas.aestronglyMeasurable
  exact .of_forall fun z=>by
    have hb (l : Paper.Overlap) :
        ‖cavityScalarFutureCovariance β μ z.2 z.1 l*cavityRestResidualCovariance D μ a z.2 z.1 l‖ ≤ (1:ℝ):=by
      rw [norm_mul]
      exact (mul_le_mul (cavityScalarFutureCovariance_norm_le β μ _ _ _)
        (cavityRestResidualCovariance_norm_le D μ a _ _ _) (norm_nonneg _) zero_le_one).trans_eq
          (one_mul _)
    simpa only [one_mul] using norm_integral_le_of_norm_le_const
      (μ:=parisiFreeMeasure μ a) (.of_forall hb)

 theorem cavityResponseFutureRemainder_integral_eq_neg_penalty (β : ℝ) (hβ : β≠0)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) :
    (∫p,cavityResponseFutureRemainder β D μ a p ∂parisiFreeMeasure μ a)=
      -cavityResidualPenalty β D μ a := by
  have hi:=integrable_cavityResidualKernel_double β D μ a
  calc
    _=-(∫p,∫r,∫l,cavityScalarFutureCovariance β μ r p l*cavityRestResidualCovariance D μ a r p l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a):=by
      simp_rw [cavityResponseFutureRemainder_eq_residual_integral β hβ D μ a,integral_neg]
    _=-(∫r,∫p,∫l,cavityScalarFutureCovariance β μ r p l*cavityRestResidualCovariance D μ a r p l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a):=
      congrArg Neg.neg (integral_integral_swap hi)
    _=-cavityResidualPenalty β D μ a:=by
      congr 1
      unfold cavityResidualPenalty cavityResidualPenaltyAt
      apply integral_congr_ae
      exact .of_forall fun r=>by
        have hmap : Measurable (fun z : Paper.Overlap×Paper.Overlap=>(r,z)):=
          measurable_const.prodMk measurable_id
        have hm:=((measurable_cavityScalarFutureCovariance β μ).comp
          hmap).mul
          ((measurable_cavityRestResidualCovariance D μ a).comp
            hmap)
        have hb (z : Paper.Overlap×Paper.Overlap) :
            ‖cavityScalarFutureCovariance β μ r z.1 z.2*cavityRestResidualCovariance D μ a r z.1 z.2‖ ≤ (1:ℝ):=by
          rw [norm_mul]
          exact (mul_le_mul (cavityScalarFutureCovariance_norm_le β μ _ _ _)
            (cavityRestResidualCovariance_norm_le D μ a _ _ _) (norm_nonneg _) zero_le_one).trans_eq
              (one_mul _)
        have hW : Integrable (fun z : Paper.Overlap×Paper.Overlap=>
            cavityScalarFutureCovariance β μ r z.1 z.2*cavityRestResidualCovariance D μ a r z.1 z.2)
            ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)):=
          (integrable_const 1).mono' hm.aestronglyMeasurable (.of_forall hb)
        exact (integral_prod _ hW).symm

 theorem integrable_cavityResponseFutureRemainder (β : ℝ) (hβ : β≠0)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) :
    Integrable (cavityResponseFutureRemainder β D μ a) (parisiFreeMeasure μ a):=by
  have hi:=(integrable_cavityResidualKernel_double β D μ a).integral_prod_left.neg
  exact hi.congr (.of_forall fun p=>(cavityResponseFutureRemainder_eq_residual_integral β hβ D μ a p).symm)

 theorem cavityResponseFutureRemainder_half_integral (β : ℝ) (hβ : β≠0)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) :
    (1/2:ℝ)*(∫p,cavityResponseFutureRemainder β D μ a p ∂parisiFreeMeasure μ a)=
      -cavityResidualPenalty β D μ a/2 := by
  rw [cavityResponseFutureRemainder_integral_eq_neg_penalty β hβ D μ a]
  ring

 theorem cavityResponseFutureRemainder_integral_nonpos (β : ℝ) (hβ : β≠0)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) :
    (∫p,cavityResponseFutureRemainder β D μ a p ∂parisiFreeMeasure μ a)≤0 := by
  rw [cavityResponseFutureRemainder_integral_eq_neg_penalty β hβ D μ a]
  exact neg_nonpos.mpr (cavityResidualPenalty_nonneg β D μ a)

end QuantitativeFollowup
