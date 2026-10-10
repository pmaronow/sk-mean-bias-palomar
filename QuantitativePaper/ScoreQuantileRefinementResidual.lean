module
public import QuantitativeFollowup.MeanCovarianceResidual
public import QuantitativeFollowup.MeanDirectionCovariance
public import QuantitativeFollowup.VectorQuantileSetVariance
public import QuantitativePaper.VectorLocalScoreVariance

@[expose] public section

/-! Actual conditional score covariance on a threshold quantile window.
The dyadic mean-increment estimate is optimized at the physical scale
M u². Its residual budget is the alpha-squared term required to refine
the variance of the terminal-spin score, rather than its conditional mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativeFollowup
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_mean_covariance_residual_threshold (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (p q : Paper.Overlap) (hpq : p≤q) (hq : q∈(parisiFreeMeasure μ s).support)
    (u : ℝ) (hu : 0<u) (hup : u≤Paper.parisiCDF μ p) :
    vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le p q≤
      56*(1+logPlus ((n:ℝ)*((1-t)*β^2)*u^2))^2/
        ((n:ℝ)*((1-t)*β^2)*u^2) := by
  let M:=(n:ℝ)*((1-t)*β^2)
  have hM : 0<M:=mul_pos (Nat.cast_pos.mpr hn)
    (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  let A:=Paper.parisiCDF μ (dyadicOverlap p q hpq 1)
  have hmid : p≤dyadicOverlap p q hpq 1:=by
    simpa only [dyadicOverlap_zero] using monotone_dyadicOverlap p q hpq (Nat.zero_le 1)
  have hA : u≤A:=hup.trans (Paper.parisiCDF_monotone μ hmid)
  have hden : 0<M*u^2:=mul_pos hM (sq_pos_of_pos hu)
  have hall : ∀K : ℕ,1≤K→vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le p q≤
      (K+1:ℝ)*(4*K/((M*u^2)*1^2)+2*((q:ℝ)-p)*(1/2:ℝ)^K):=by
    intro K hK
    have hb:=vector_mean_covariance_dyadic_bound hn μ s hs hμ β t s hβ ht hs.1.le hmin p q hpq hq K
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    simp only [one_pow,mul_one]
    apply div_le_div_of_nonneg_left (by positivity) hden
    simpa only [one_pow,mul_one] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le hA 2) hM.le
  have hh := dyadic_residual_optimized_bound (M:=M*u^2) (A:=1)
    hden (by norm_num) le_rfl (sub_nonneg.mpr hpq) hall
  simp only [one_pow,mul_one] at hh
  have hd1 : (q:ℝ)-p≤1:=by linarith [q.property.2,p.property.1]
  have hlog : logPlus ((M*u^2)*((q:ℝ)-p))≤logPlus (M*u^2):=
    logPlus_le_of_nonneg_le (mul_nonneg hden.le (sub_nonneg.mpr hpq))
      ((mul_le_mul_of_nonneg_left hd1 hden.le).trans_eq (mul_one _))
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hden.le
  have hp : (1+logPlus ((M*u^2)*((q:ℝ)-p)))^2≤(1+logPlus (M*u^2))^2:=
    pow_le_pow_left₀ (by linarith [logPlus_nonneg ((M*u^2)*((q:ℝ)-p))])
      (add_le_add_right hlog 1) 2
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

theorem quantileWindowKernel_eq_setKernel (μ : Paper.ParisiMeasure)
    (s v x : ℝ) (hxv : 0≤v-x) :
  quantileWindowKernel μ s v x=quantileSetKernel μ s (Ioc (v-x) v) x := by
  funext q
  simp only [quantileWindowKernel,quantileSetKernel,quantileWindowMeasure,quantileSetMeasure,
    max_eq_right hxv]

theorem vector_quantile_window_score_variance_threshold (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v x u : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hDom : Ioc (v-x) v⊆Ioc (0:ℝ) (1-s)) (hx : 0<x) (hxv : 0≤v-x) (hu : 0<u)
    (hThreshold : ∀ᵐw ∂volume.restrict (Ioc (v-x) v),
      u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w)) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le (quantileWindowKernel μ s v x))
      (vectorMeasureSpinPathLaw μ β t s ht.le)≤1/((n:ℝ)*((1-t)*β^2)*u*x) := by
  rw [quantileWindowKernel_eq_setKernel μ s v x hxv]
  have he:=vector_quantile_set_score_variance hn μ s β t hβ ht hs hμ hmin
    (Ioc (v-x) v) x u hDom hx (by rw [Real.volume_real_Ioc];simp only [sub_sub_cancel];exact max_eq_left hx.le)
    hu hThreshold
  rw [variance_vectorCenteredKernelScore μ s β t s ht.le _
    (measurable_quantileSetKernel μ s _ _)] at he
  exact he

theorem vector_quantile_window_residual_threshold (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v x u : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hv : v∈Ioc (0:ℝ) (1-s)) (hx : 0<x) (hxv : 0≤v-x) (hu : 0<u)
    (hThreshold : ∀ᵐw ∂volume.restrict (Ioc (v-x) v),
      u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w)) :
    (∫w,vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le
      (parisiPaddedFreeQuantile μ s w) (parisiFreeQuantile μ s v) ∂quantileWindowAveraging v x)≤
        56*(1+logPlus ((n:ℝ)*((1-t)*β^2)*u^2))^2/
          ((n:ℝ)*((1-t)*β^2)*u^2) := by
  letI:=quantileWindowAveraging_probability v x hx
  have hi:=integrable_quantileWindowMeanCovarianceIncrement (n:=n) μ s β t s v x ht.le hx
    (parisiFreeQuantile μ s v)
  have htW : ∀ᵐw ∂quantileWindowAveraging v x,
      u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w):=
    Measure.ae_smul_measure hThreshold _
  have hbound : ∀ᵐw ∂quantileWindowAveraging v x,
      vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le
        (parisiPaddedFreeQuantile μ s w) (parisiFreeQuantile μ s v)≤
          56*(1+logPlus ((n:ℝ)*((1-t)*β^2)*u^2))^2/
            ((n:ℝ)*((1-t)*β^2)*u^2):=by
    filter_upwards [htW,Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _] with w hw hwi
    have hw0 : 0<w:=hxv.trans_lt hwi.1
    have hp : parisiPaddedFreeQuantile μ s w=parisiFreeQuantile μ s w:=by
      simp only [parisiPaddedFreeQuantile,ite_eq_right (not_le.mpr hw0)]
    rw [hp]
    exact vector_mean_covariance_residual_threshold hn μ s ⟨hs.1,hs.2.le⟩ hμ β t hβ ht hmin _ _
      (parisiFreeQuantile_monotone μ s hwi.2)
      (parisiFreeQuantile_mem_support μ s ⟨hs.1.le,hs.2.le⟩ hv) u hu hw
  have h:=integral_mono_ae hi (integrable_const _) hbound
  simpa only [integral_const,probReal_univ,one_smul] using h

theorem vector_mean_direction_covariance_window_threshold (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v x u : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hv : v∈Ioc (0:ℝ) (1-s)) (hx : 0<x) (hxv : 0≤v-x) (hu : 0<u)
    (hDom : Ioc (v-x) v⊆Ioc (0:ℝ) (1-s))
    (hThreshold : ∀ᵐw ∂volume.restrict (Ioc (v-x) v),
      u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w)) :
    vectorMeanDirectionCovariance (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)≤
      2/((n:ℝ)*((1-t)*β^2)*u*x)+
        112*(1+logPlus ((n:ℝ)*((1-t)*β^2)*u^2))^2/
          ((n:ℝ)*((1-t)*β^2)*u^2) := by
  have hbar:=vectorMeasureWeightedScore_kernel_covariance_le_variance (n:=n)
    μ s β t hβ ht ⟨hs.1.le,hs.2.le⟩ (quantileWindowKernel μ s v x)
    (measurable_quantileWindowKernel μ s v x) (1/x) (by positivity)
    (fun q=>by rw [abs_of_nonneg (quantileWindowKernel_nonneg_le μ s v x hx q).1]
               exact (quantileWindowKernel_nonneg_le μ s v x hx q).2)
    (parisiFreeQuantile μ s v) (ae_quantileWindowKernel_past μ s v x)
  have he : vectorQuantileWindowMean (n:=n) μ s β t v x ht.le=
      vectorMeasureKernelMean μ s β t ht.le (quantileWindowKernel μ s v x):=by
    funext sample
    exact vectorQuantileWindowMean_eq_kernel μ s β t v x ht.le hv.2 hx sample
  change vectorDirectionCovariance μ β t s ht.le
    (vectorMeasureKernelMean μ s β t ht.le (quantileWindowKernel μ s v x))
    (parisiFreeQuantile μ s v)/(n:ℝ)^2≤_ at hbar
  rw [←he] at hbar
  have hsplit:=vector_quantile_window_covariance_split (n:=n) μ s β t s v x hβ ht hx
    (parisiFreeQuantile μ s v)
  have h2 : 2*vectorDirectionCovariance μ β t s ht.le
      (vectorQuantileWindowMean (n:=n) μ s β t v x ht.le) (parisiFreeQuantile μ s v)/(n:ℝ)^2≤
      2*variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le (quantileWindowKernel μ s v x))
        (vectorMeasureSpinPathLaw μ β t s ht.le):=by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hbar (by norm_num : (0:ℝ)≤2)
  have hV:=vector_quantile_window_score_variance_threshold hn μ s β t v x u hβ ht hs hμ hmin hDom hx hxv hu hThreshold
  have hR:=vector_quantile_window_residual_threshold hn μ s β t v x u hβ ht hs hμ hmin hv hx hxv hu hThreshold
  calc
    _≤2*variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le (quantileWindowKernel μ s v x))
        (vectorMeasureSpinPathLaw μ β t s ht.le)+2*(∫w,vectorMeanCovarianceIncrement μ β t s ht.le
          (parisiPaddedFreeQuantile μ s w) (parisiFreeQuantile μ s v) ∂quantileWindowAveraging v x):=
      hsplit.trans (add_le_add h2 le_rfl)
    _≤2*(1/((n:ℝ)*((1-t)*β^2)*u*x))+2*(56*(1+logPlus ((n:ℝ)*((1-t)*β^2)*u^2))^2/
        ((n:ℝ)*((1-t)*β^2)*u^2)):=
      add_le_add (mul_le_mul_of_nonneg_left hV (by norm_num)) (mul_le_mul_of_nonneg_left hR (by norm_num))
    _=_:=by ring

end QuantitativePaper
