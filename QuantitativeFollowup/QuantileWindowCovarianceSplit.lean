module
public import QuantitativeFollowup.QuantileWindowMean
public import QuantitativeFollowup.QuantileWindowResidual
public import FourPapersCommon.PositiveQuadraticIntegral

@[expose] public section

/-! The actual covariance split into a padded quantile-window mean and
its residual.  Matrix Jensen is applied sample by sample, and genuine
bounded product integrability justifies the expectation/window Fubini step. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeanDirectionCovariance (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) : ℝ :=
  vectorDirectionCovariance (n:=n) μ β t a ht (vectorMeasureSpinMean μ β t ht q) q/(n:ℝ)^2

def vectorQuantileResidualQuadratic (μ : Paper.ParisiMeasure) (s β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (z : ℝ×VectorDisorderBrownianSample n) : ℝ :=
  vectorMeasureCovarianceQuadratic μ β t a ht q z.2
    (vectorMeasureSpinMean μ β t ht q z.2-
      vectorMeasureSpinMean μ β t ht (parisiPaddedFreeQuantile μ s z.1) z.2)

theorem measurable_vectorQuantileResidualQuadratic (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    Measurable (vectorQuantileResidualQuadratic (n:=n) μ s β t a ht q) := by
  have hM : Measurable (vectorMeasureSpinMean (n:=n) μ β t ht q):=
    (adapted_vectorMeasureSpinMean μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl
  have hD := (hM.comp measurable_snd).sub (measurable_padded_vectorMeasureSpinMean μ s β t ht)
  unfold vectorQuantileResidualQuadratic vectorMeasureCovarianceQuadratic
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact (((measurable_vectorMeasureSpinCovariance_entry μ β t a ht q i j).comp measurable_snd).mul
    (((EuclideanSpace.proj i).continuous.measurable).comp hD)).mul
    (((EuclideanSpace.proj j).continuous.measurable).comp hD)

theorem integrable_vectorQuantileResidualQuadratic (μ : Paper.ParisiMeasure)
    (s β t a v x : ℝ) (ht : t≤1) (hx : 0<x) (q : Paper.Overlap) :
    Integrable (vectorQuantileResidualQuadratic (n:=n) μ s β t a ht q)
      ((quantileWindowAveraging v x).prod (vectorMeasureDisorderTilt μ β t a)) := by
  let :=quantileWindowAveraging_probability v x hx
  let :=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hm:=measurable_vectorQuantileResidualQuadratic (n:=n) μ s β t a ht q
  apply (integrable_const (8*(n:ℝ)^2)).mono' hm.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).mpr
  filter_upwards with w
  filter_upwards [vectorMeasureSpinCovariance_entry_bound μ β t a ht q] with sample hc
  let D:=vectorMeasureSpinMean μ β t ht q sample-
    vectorMeasureSpinMean μ β t ht (parisiPaddedFreeQuantile μ s w) sample
  have hD (i : Fin n) : |D i|≤2 := by
    change |vectorMeasureSpinMean μ β t ht q sample i-vectorMeasureSpinMean μ β t ht (parisiPaddedFreeQuantile μ s w) sample i|≤2
    exact (abs_sub _ _).trans (by linarith [vectorMeasureSpinMean_component_bound μ β t ht q sample i,
      vectorMeasureSpinMean_component_bound μ β t ht (parisiPaddedFreeQuantile μ s w) sample i])
  rw [Real.norm_eq_abs]
  unfold vectorQuantileResidualQuadratic vectorMeasureCovarianceQuadratic
  calc
    _≤∑i : Fin n,∑j : Fin n,|vectorMeasureSpinCovariance μ β t a ht q sample i j*D i*D j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _=>Finset.abs_sum_le_sum_abs _ _)
    _≤∑_i : Fin n,∑_j : Fin n,(8:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_mul]
      have h:=mul_le_mul (mul_le_mul (hc i j) (hD i) (abs_nonneg _) (by norm_num))
        (hD j) (abs_nonneg _) (by norm_num : (0:ℝ)≤2*2)
      norm_num only at h
      exact h
    _=8*(n:ℝ)^2 := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

theorem vector_quantile_window_covariance_split (μ : Paper.ParisiMeasure)
    (s β t a v x : ℝ) (hβ : β≠0) (ht : t<1) (hx : 0<x) (q : Paper.Overlap) :
    vectorMeanDirectionCovariance (n:=n) μ β t a ht.le q≤
      2*vectorDirectionCovariance (n:=n) μ β t a ht.le (vectorQuantileWindowMean (n:=n) μ s β t v x ht.le) q/(n:ℝ)^2+
      2*∫w,vectorMeanCovarianceIncrement (n:=n) μ β t a ht.le (parisiPaddedFreeQuantile μ s w) q
        ∂quantileWindowAveraging v x := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  let W:=quantileWindowAveraging v x
  let :=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let :=quantileWindowAveraging_probability v x hx
  have hi:=integrable_vectorQuantileResidualQuadratic (n:=n) μ s β t a v x ht.le hx q
  have hb : MemLp (vectorQuantileWindowMean (n:=n) μ s β t v x ht.le) 2 P :=
    MemLp.of_bound (measurable_vectorQuantileWindowMean μ s β t v x ht.le).aestronglyMeasurable
      (Real.sqrt (n:ℝ)) (.of_forall (norm_vectorQuantileWindowMean_le μ s β t v x ht.le hx))
  have hleft:=integrable_vectorMeasureRandomCovariance (n:=n) μ β t a ht.le q (vectorMeasureSpinMean μ β t ht.le q)
    (memLp_vectorMeasureSpinMean (n:=n) μ β t a ht.le q)
  have hbar:=integrable_vectorMeasureRandomCovariance μ β t a ht.le q _ hb
  have hright:= (hbar.const_mul 2).add (hi.integral_prod_right.const_mul 2)
  have h:=integral_mono_ae hleft hright (show
      (fun sample=>vectorMeasureCovarianceQuadratic μ β t a ht.le q sample (vectorMeasureSpinMean μ β t ht.le q sample))≤ᵐ[P]
      (fun sample=>2*vectorMeasureCovarianceQuadratic μ β t a ht.le q sample
        (vectorQuantileWindowMean μ s β t v x ht.le sample)+
          2*∫w,vectorQuantileResidualQuadratic μ s β t a ht.le q (w,sample) ∂W) from by
    filter_upwards [vectorMeasure_matrix_order μ β t a hβ ht q,hi.prod_left_ae] with sample hc hres
    have hvm : Measurable (fun w : ℝ=>vectorMeasureSpinMean μ β t ht.le (parisiPaddedFreeQuantile μ s w) sample) := by
      have hh:=(measurable_padded_vectorMeasureSpinMean (n:=n) μ s β t ht.le).comp
        (measurable_id.prodMk (measurable_const (a:=sample)))
      simpa only [Function.comp_def,id_eq] using hh
    have hv : Integrable (fun w : ℝ=>vectorMeasureSpinMean μ β t ht.le (parisiPaddedFreeQuantile μ s w) sample) W :=
      (integrable_const (Real.sqrt (n:ℝ))).mono' hvm.aestronglyMeasurable
        (.of_forall fun w=>norm_vectorMeasureSpinMean_le μ β t ht.le (parisiPaddedFreeQuantile μ s w) sample)
    exact positive_matrix_quadratic_mean_split W _ hc.1 _ _ hv hres)
  simp only [Pi.add_apply] at h
  have hswap:=integral_integral_swap (μ:=W) (ν:=P)
    (f:=fun w sample=>vectorQuantileResidualQuadratic μ s β t a ht.le q (w,sample)) hi
  rw [integral_add (hbar.const_mul 2) (hi.integral_prod_right.const_mul 2),
    integral_const_mul,integral_const_mul,←hswap] at h
  have hn : 0≤(n:ℝ)^2:=sq_nonneg _
  have he:=div_le_div_of_nonneg_right h hn
  change _≤(2*vectorDirectionCovariance (n:=n) μ β t a ht.le (vectorQuantileWindowMean (n:=n) μ s β t v x ht.le) q+
    2*∫w,vectorDirectionCovariance μ β t a ht.le
      (fun sample=>vectorMeasureSpinMean μ β t ht.le q sample-
        vectorMeasureSpinMean μ β t ht.le (parisiPaddedFreeQuantile μ s w) sample) q ∂W)/(n:ℝ)^2 at he
  simpa only [vectorMeanDirectionCovariance,vectorMeanCovarianceIncrement,vectorDirectionCovariance,W,add_div,mul_div_assoc,
    ←integral_div] using he

end QuantitativeFollowup
