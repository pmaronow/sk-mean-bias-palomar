module
public import QuantitativeFollowup.FollowupCavityRestResidualCovariance

@[expose] public section

/-! The actual scalar/rest covariance penalty is an honest nonnegative
integrable quantity. Its sign comes from the independent product-space
square, with both constructed future conditional means retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128

theorem measurable_cavityScalarFutureCovariance (β : ℝ) (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×(Paper.Overlap×Paper.Overlap)=>
      cavityScalarFutureCovariance β μ z.1 z.2.1 z.2.2) := by
  have hp := (measurable_cavityScalarFutureCenteredTail β μ).comp
    (show Measurable (fun z : (Paper.Overlap×(Paper.Overlap×Paper.Overlap))×Paper.BrownianSample=>
      (z.1.1,(z.2,z.1.2.1))) from by fun_prop)
  have hl := (measurable_cavityScalarFutureCenteredTail β μ).comp
    (show Measurable (fun z : (Paper.Overlap×(Paper.Overlap×Paper.Overlap))×Paper.BrownianSample=>
      (z.1.1,(z.2,z.1.2.2))) from by fun_prop)
  exact (hp.mul hl).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_cavityRestResidualCovariance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measurable (fun z : Paper.Overlap×(Paper.Overlap×Paper.Overlap)=>
      cavityRestResidualCovariance D μ a z.1 z.2.1 z.2.2) := by
  have hp := (measurable_cavityRestFutureResidualTail D μ).comp
    (show Measurable (fun z : (Paper.Overlap×(Paper.Overlap×Paper.Overlap))×AnisotropicDisorderBrownianSample n=>
      (z.1.1,(z.2,z.1.2.1))) from by fun_prop)
  have hl := (measurable_cavityRestFutureResidualTail D μ).comp
    (show Measurable (fun z : (Paper.Overlap×(Paper.Overlap×Paper.Overlap))×AnisotropicDisorderBrownianSample n=>
      (z.1.1,(z.2,z.1.2.2))) from by fun_prop)
  exact (hp.mul hl).stronglyMeasurable.integral_prod_right'.measurable

theorem cavityScalarFutureCovariance_norm_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p l : Paper.Overlap) : ‖cavityScalarFutureCovariance β μ r p l‖≤1 := by
  have hb (ω : Paper.BrownianSample) :
      ‖cavityScalarFutureCenteredTail β μ r (ω,p)*cavityScalarFutureCenteredTail β μ r (ω,l)‖≤(1:ℝ) := by
    rw [norm_mul]
    exact (mul_le_mul (cavityScalarFutureCenteredTail_norm_le β μ r _)
      (cavityScalarFutureCenteredTail_norm_le β μ r _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  simpa only [cavityScalarFutureCovariance,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure) (.of_forall hb))

theorem cavityRestResidualCovariance_norm_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p l : Paper.Overlap) :
    ‖cavityRestResidualCovariance D μ a r p l‖≤1 := by
  have hb (ω : AnisotropicDisorderBrownianSample n) :
      ‖cavityRestFutureResidualTail D μ r (ω,p)*cavityRestFutureResidualTail D μ r (ω,l)‖≤(1:ℝ) := by
    rw [norm_mul]
    exact (mul_le_mul (cavityRestFutureResidualTail_norm_le D μ r _)
      (cavityRestFutureResidualTail_norm_le D μ r _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  simpa only [cavityRestResidualCovariance,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=anisotropicMeasureSampleLaw D μ a) (.of_forall hb))

def cavityResidualPenaltyAt (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) : ℝ :=
  ∫pq : Paper.Overlap×Paper.Overlap,cavityScalarFutureCovariance β μ r pq.1 pq.2*
    cavityRestResidualCovariance D μ a r pq.1 pq.2
    ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)

def cavityResidualPenalty (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : ℝ :=
  ∫r,cavityResidualPenaltyAt β D μ a r ∂parisiFreeMeasure μ a

theorem cavityResidualPenaltyAt_eq_square (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    cavityResidualPenaltyAt β D μ a r=
      ∫ω : Paper.BrownianSample×AnisotropicDisorderBrownianSample n,
        (∫p,cavityScalarFutureCenteredTail β μ r (ω.1,p)*
          cavityRestFutureResidualTail D μ r (ω.2,p) ∂parisiFreeMeasure μ a)^2
        ∂canonicalBrownianMeasure.prod (anisotropicMeasureSampleLaw D μ a) := by
  exact (bounded_product_kernel_square (parisiFreeMeasure μ a)
    canonicalBrownianMeasure (anisotropicMeasureSampleLaw D μ a)
    (cavityScalarFutureCenteredTail β μ r) (cavityRestFutureResidualTail D μ r)
    ((measurable_cavityScalarFutureCenteredTail β μ).comp (measurable_const.prodMk measurable_id))
    ((measurable_cavityRestFutureResidualTail D μ).comp (measurable_const.prodMk measurable_id))
    1 1 (by norm_num) (by norm_num)
    (cavityScalarFutureCenteredTail_norm_le β μ r)
    (cavityRestFutureResidualTail_norm_le D μ r)).symm

theorem cavityResidualPenaltyAt_nonneg (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    0≤cavityResidualPenaltyAt β D μ a r := by
  rw [cavityResidualPenaltyAt_eq_square]
  exact integral_nonneg fun _=>sq_nonneg _

theorem measurable_cavityResidualPenaltyAt (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measurable (cavityResidualPenaltyAt β D μ a) :=
  ((measurable_cavityScalarFutureCovariance β μ).mul
    (measurable_cavityRestResidualCovariance D μ a)).stronglyMeasurable.integral_prod_right'.measurable

theorem cavityResidualPenaltyAt_norm_le (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    ‖cavityResidualPenaltyAt β D μ a r‖≤
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)).real univ := by
  have hb (pq : Paper.Overlap×Paper.Overlap) :
      ‖cavityScalarFutureCovariance β μ r pq.1 pq.2*cavityRestResidualCovariance D μ a r pq.1 pq.2‖≤(1:ℝ) := by
    rw [norm_mul]
    exact (mul_le_mul (cavityScalarFutureCovariance_norm_le β μ r _ _)
      (cavityRestResidualCovariance_norm_le D μ a r _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  simpa only [cavityResidualPenaltyAt,one_mul] using (norm_integral_le_of_norm_le_const
    (μ:=(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) (.of_forall hb))

theorem integrable_cavityResidualPenaltyAt (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Integrable (cavityResidualPenaltyAt β D μ a) (parisiFreeMeasure μ a) :=
  (integrable_const (((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)).real univ)).mono'
    (measurable_cavityResidualPenaltyAt β D μ a).aestronglyMeasurable
    (.of_forall (cavityResidualPenaltyAt_norm_le β D μ a))

theorem cavityResidualPenalty_nonneg (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : 0≤cavityResidualPenalty β D μ a :=
  integral_nonneg (cavityResidualPenaltyAt_nonneg β D μ a)

end QuantitativeFollowup
