module
public import QuantitativeFollowup.FollowupCavityRestProcess
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The actual centered rest self-overlap covariance has finite positive
trace equal to the integrated native variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def cavityRestVariance (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) : ℝ:=
  ∫q : Paper.Overlap,variance (cavityRestSelfOverlap D μ q)
    (anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a

theorem measurable_cavityRestSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (cavityRestSelfOverlap D μ q) := by
  have hi : Measurable (fun ω : AnisotropicDisorderBrownianSample n=>(q,ω)):=
    measurable_const.prodMk measurable_id
  have hh := (measurable_uncurry_cavityRestSelfOverlap D μ).comp hi
  simpa only [Function.comp_def] using hh

theorem cavityRest_pointwise_variance_le_one (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    variance (cavityRestSelfOverlap D μ q) (anisotropicMeasureSampleLaw D μ a)≤1 := by
  rw [variance_eq_integral (measurable_cavityRestSelfOverlap D μ q).aemeasurable]
  have hm := (measurable_cavityRestSelfOverlap D μ q).sub_const
    (∫ω,cavityRestSelfOverlap D μ q ω ∂anisotropicMeasureSampleLaw D μ a)
  have hb (ω : AnisotropicDisorderBrownianSample n) :
      (cavityRestSelfOverlap D μ q ω-
        ∫ω,cavityRestSelfOverlap D μ q ω ∂anisotropicMeasureSampleLaw D μ a)^2≤1 := by
    rw [←cavityRestOverlapMean_apply]
    have ht := (cavityRestCenteredOverlapPath D μ a ω).norm_coe_le_norm q
    have hh := ht.trans (cavityRestCenteredOverlapPath_norm_le D μ a ω)
    change ‖cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q‖≤1 at hh
    simpa only [sq_abs,one_pow,Real.norm_eq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hi : Integrable (fun ω=>
      (cavityRestSelfOverlap D μ q ω-
        ∫ω,cavityRestSelfOverlap D μ q ω ∂anisotropicMeasureSampleLaw D μ a)^2)
      (anisotropicMeasureSampleLaw D μ a) :=
    (integrable_const 1).mono' (hm.pow_const 2).aestronglyMeasurable
      (.of_forall fun ω=>by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact hb ω)
  exact (integral_mono hi (integrable_const 1) hb).trans_eq (by simp)

theorem integrable_cavityRest_centered_product (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Integrable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      (cavityRestSelfOverlap D μ z.1 z.2-cavityRestOverlapMean D μ a z.1)^2)
      ((parisiFreeMeasure μ a).prod (anisotropicMeasureSampleLaw D μ a)) := by
  have hm := ((measurable_uncurry_cavityRestSelfOverlap D μ).sub
    ((cavityRestOverlapMean D μ a).continuous.measurable.comp measurable_fst)).pow_const 2
  apply (integrable_const 1).mono' hm.aestronglyMeasurable
  exact .of_forall fun z=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    change (cavityRestSelfOverlap D μ z.1 z.2-cavityRestOverlapMean D μ a z.1)^2≤1
    have ht := (cavityRestCenteredOverlapPath D μ a z.2).norm_coe_le_norm z.1
    have hh := ht.trans (cavityRestCenteredOverlapPath_norm_le D μ a z.2)
    change ‖cavityRestSelfOverlap D μ z.1 z.2-cavityRestOverlapMean D μ a z.1‖≤1 at hh
    simpa only [sq_abs,one_pow,Real.norm_eq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem cavityRestVariance_eq_integral_norm_sq (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    cavityRestVariance D μ a=
      ∫ω,‖cavityRestEndpointProcess D μ a ω‖^2 ∂anisotropicMeasureSampleLaw D μ a := by
  have hfub := integral_integral_swap
    (f:=fun q ω=>(cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q)^2)
    (integrable_cavityRest_centered_product D μ a)
  calc
    cavityRestVariance D μ a=
        ∫q : Paper.Overlap,∫ω,
          (cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q)^2
          ∂anisotropicMeasureSampleLaw D μ a ∂parisiFreeMeasure μ a := by
      apply integral_congr_ae
      exact .of_forall fun q=>by
        dsimp only
        rw [variance_eq_integral (measurable_cavityRestSelfOverlap D μ q).aemeasurable,
          cavityRestOverlapMean_apply]
    _=∫ω,∫q : Paper.Overlap,
          (cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q)^2
          ∂parisiFreeMeasure μ a ∂anisotropicMeasureSampleLaw D μ a := hfub
    _=∫ω,‖cavityRestEndpointProcess D μ a ω‖^2 ∂anisotropicMeasureSampleLaw D μ a := by
      apply integral_congr_ae
      exact .of_forall fun ω=>by
        change _=‖(cavityRestEndpointProcess D μ a ω : Lp ℝ 2 (parisiFreeMeasure μ a))‖^2
        rw [cavityRestEndpointProcess_coe D μ a hone ω]
        unfold cavityRestL2Process
        rw [overlapCenteredL2Process_norm_sq]
        rfl

theorem cavityRestVariance_nonneg (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : 0≤cavityRestVariance D μ a :=
  integral_nonneg fun _=>variance_nonneg _ _

theorem cavityRestVariance_le_one (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    cavityRestVariance D μ a≤1 := by
  rw [cavityRestVariance_eq_integral_norm_sq D μ a hone]
  have hbound (ω : AnisotropicDisorderBrownianSample n) :
      ‖cavityRestEndpointProcess D μ a ω‖^2≤(parisiFreeMeasure μ a).real univ := by
    change ‖(cavityRestEndpointProcess D μ a ω : Lp ℝ 2 (parisiFreeMeasure μ a))‖^2≤_
    rw [cavityRestEndpointProcess_coe D μ a hone ω,cavityRestL2Process,
      overlapCenteredL2Process_norm_sq]
    have hb (q : Paper.Overlap) :
        (cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q)^2≤1 := by
      have ht := (cavityRestCenteredOverlapPath D μ a ω).norm_coe_le_norm q
      have hh := ht.trans (cavityRestCenteredOverlapPath_norm_le D μ a ω)
      change ‖cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q‖≤1 at hh
      simpa only [sq_abs,one_pow,Real.norm_eq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) hh 2
    have hm : Measurable (fun q : Paper.Overlap=>
      (cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q)^2):=
      (cavityRestCenteredOverlapPath D μ a ω).continuous.measurable.pow_const 2
    have hint := (integrable_const (μ:=parisiFreeMeasure μ a) (1:ℝ)).mono' hm.aestronglyMeasurable
      (.of_forall fun q=>by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact hb q)
    exact (integral_mono hint (integrable_const 1) hb).trans_eq (by simp)
  have hint := (memLp_cavityRestEndpointProcess D μ a).integrable_norm_pow
    (by norm_num : (2:ℕ)≠0)
  calc
    _≤∫_ω,(parisiFreeMeasure μ a).real univ ∂anisotropicMeasureSampleLaw D μ a :=
      integral_mono hint (integrable_const _) hbound
    _=(parisiFreeMeasure μ a).real univ := by simp
    _=1-a := by
      rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
    _≤1 := by linarith [ha.1]

def cavityRestCovariance (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) : endpointFixedL2 (parisiFreeMeasure μ a)→L[ℝ]
      endpointFixedL2 (parisiFreeMeasure μ a):=
  overlapProcessCovariance (anisotropicMeasureSampleLaw D μ a) (parisiFreeMeasure μ a)
    (cavityRestOverlapPath D μ)

theorem cavityRestCovariance_isPositiveTraceClass (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : IsPositiveTraceClass (cavityRestCovariance D μ a):=
  overlapProcessCovariance_isPositiveTraceClass _ _ _ (measurable_cavityRestOverlapPath D μ)
    1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)

theorem cavityRestCovariance_trace (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    HasFinitePositiveTrace (cavityRestCovariance D μ a) (cavityRestVariance D μ a) := by
  rw [cavityRestVariance_eq_integral_norm_sq D μ a hone]
  exact overlapProcessCovariance_hasFinitePositiveTrace _ _ _
    (measurable_cavityRestOverlapPath D μ) 1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)

def cavityRestCovarianceFull (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) : Lp ℝ 2 (parisiFreeMeasure μ a)→L[ℝ]Lp ℝ 2 (parisiFreeMeasure μ a):=
  overlapFullProcessCovariance (anisotropicMeasureSampleLaw D μ a) (parisiFreeMeasure μ a)
    (cavityRestOverlapPath D μ)

theorem cavityRestCovarianceFull_range (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0)
    (x : Lp ℝ 2 (parisiFreeMeasure μ a)) :
    cavityRestCovarianceFull D μ a x∈endpointFixedL2 (parisiFreeMeasure μ a) :=
  overlapFullProcessCovariance_range_endpoint _ _ _ (measurable_cavityRestOverlapPath D μ)
    1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)
    (cavityRestSelfOverlap_zero D μ) hone x

theorem cavityRestCovarianceFull_isPositiveTraceClass (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : IsPositiveTraceClass (cavityRestCovarianceFull D μ a):=
  overlapFullProcessCovariance_isPositiveTraceClass _ _ _ (measurable_cavityRestOverlapPath D μ)
    1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)

theorem cavityRestCovarianceFull_trace (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    HasFinitePositiveTrace (cavityRestCovarianceFull D μ a) (cavityRestVariance D μ a) := by
  have ht := overlapFullProcessCovariance_hasFinitePositiveTrace
    (anisotropicMeasureSampleLaw D μ a) (parisiFreeMeasure μ a) (cavityRestOverlapPath D μ)
    (measurable_cavityRestOverlapPath D μ) 1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)
  rw [cavityRestVariance_eq_integral_norm_sq D μ a hone]
  change HasFinitePositiveTrace
    (overlapFullProcessCovariance (anisotropicMeasureSampleLaw D μ a)
      (parisiFreeMeasure μ a) (cavityRestOverlapPath D μ)) _
  convert ht using 1
  apply integral_congr_ae
  exact .of_forall fun ω=>by
    change ‖(cavityRestEndpointProcess D μ a ω : Lp ℝ 2 (parisiFreeMeasure μ a))‖^2=_
    rw [cavityRestEndpointProcess_coe D μ a hone ω]
    rfl

theorem integral_cavityRestL2Process_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    (∫ω,cavityRestL2Process D μ a ω ∂anisotropicMeasureSampleLaw D μ a)=0 :=
  integral_overlapCenteredL2Process _ _ _ (measurable_cavityRestOverlapPath D μ)
    1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)

end QuantitativeFollowup
