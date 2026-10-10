module
public import QuantitativeFollowup.MeanDirectionCovarianceRegularity
public import HexagonPaper.MeanCovarianceResidual
public import HexagonPaper.MeanCovarianceVariance
public import QuantitativeFollowup.MeanDirectionCovariance
public import QuantitativeFollowup.QuantileWindowResidualAverage
public import QuantitativeFollowup.QuantileWindowCost
public import QuantitativeFollowup.ParisiQuantileIntegrals
public import QuantitativePaper.VectorMeasureKernelScoreVariance

@[expose] public section

/-! The literal pointwise and integrated 341 mean-direction covariance bounds, via a quarter-window proof with the stronger internal budget 212.
The quantile window, its Brownian-past conditional covariance, the score
variance, and the residual budgets all concern the actual minimizing model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup
open scoped NNReal ENNReal
namespace HexagonPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem mean_direction_budget_341 {j V R M y : ℝ} (hM : 0<M) (hy : 0<y)
    (hSplit : j≤2*V+2*R) (hV : V≤6/(M*y^2))
    (hR : R≤100*(1+logPlus M)^2/(M*y^2)) :
    j≤341*(1+logPlus M)^2/(M*y^2) := by
  have hD : 0<M*y^2:=mul_pos hM (sq_pos_of_pos hy)
  have hL : 1≤(1+logPlus M)^2:=by nlinarith [logPlus_nonneg M]
  calc
    j≤2*(6/(M*y^2))+2*(100*(1+logPlus M)^2/(M*y^2)) :=
      hSplit.trans (add_le_add (mul_le_mul_of_nonneg_left hV (by norm_num))
        (mul_le_mul_of_nonneg_left hR (by norm_num)))
    _=12/(M*y^2)+200*(1+logPlus M)^2/(M*y^2) := by ring
    _≤12*(1+logPlus M)^2/(M*y^2)+200*(1+logPlus M)^2/(M*y^2) := by
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_right (by nlinarith) hD.le
    _=212*(1+logPlus M)^2/(M*y^2) := by ring
    _≤341*(1+logPlus M)^2/(M*y^2) := by
      apply div_le_div_of_nonneg_right _ hD.le
      exact mul_le_mul_of_nonneg_right (by norm_num : (212:ℝ)≤341) (sq_nonneg _)

theorem vector_mean_direction_covariance_bound_341 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1)
    (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    {v : ℝ} (hv : v∈Ioc (0:ℝ) (1-s)) :
    vectorMeanDirectionCovariance (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)≤
      341*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*(s+v)^2) := by
  have hx : 0<(s+v)/4:=by linarith [hs.1,hv.1]
  have hM : 0<(n:ℝ)*((1-t)*β^2):=mul_pos (Nat.cast_pos.mpr hn)
    (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hbar:=vectorMeasureWeightedScore_kernel_covariance_le_variance (n:=n)
    μ s β t hβ ht ⟨hs.1.le,hs.2.le⟩ (quantileWindowKernel μ s v ((s+v)/4))
    (measurable_quantileWindowKernel μ s v ((s+v)/4)) (1/((s+v)/4)) (by positivity)
    (fun q=>by rw [abs_of_nonneg (quantileWindowKernel_nonneg_le μ s v ((s+v)/4) hx q).1]
               exact (quantileWindowKernel_nonneg_le μ s v ((s+v)/4) hx q).2)
    (parisiFreeQuantile μ s v) (ae_quantileWindowKernel_past μ s v ((s+v)/4))
  have he : vectorQuantileWindowMean (n:=n) μ s β t v ((s+v)/4) ht.le=
      vectorMeasureKernelMean μ s β t ht.le (quantileWindowKernel μ s v ((s+v)/4)) := by
    funext sample
    exact vectorQuantileWindowMean_eq_kernel μ s β t v ((s+v)/4) ht.le hv.2 hx sample
  change vectorDirectionCovariance μ β t s ht.le
    (vectorMeasureKernelMean μ s β t ht.le (quantileWindowKernel μ s v ((s+v)/4)))
    (parisiFreeQuantile μ s v)/(n:ℝ)^2≤_ at hbar
  rw [←he] at hbar
  have hsplit:=vector_quantile_window_covariance_split (n:=n) μ s β t s v ((s+v)/4)
    hβ ht hx (parisiFreeQuantile μ s v)
  have hsplit' := hsplit.trans (add_le_add
    (show 2*vectorDirectionCovariance μ β t s ht.le
      (vectorQuantileWindowMean (n:=n) μ s β t v ((s+v)/4) ht.le) (parisiFreeQuantile μ s v)/(n:ℝ)^2≤
      2*variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le
        (quantileWindowKernel μ s v ((s+v)/4))) (vectorMeasureSpinPathLaw μ β t s ht.le) from by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hbar (by norm_num : (0:ℝ)≤2)) le_rfl)
  exact mean_direction_budget_341 hM (by linarith [hs.1,hv.1]) hsplit'
    (vector_quarter_window_score_variance hn μ s β t v hβ ht hs hμ hmin hv)
    (vector_quarter_window_residual_average_bound hn μ s β t v hβ ht ⟨hs.1,hs.2.le⟩ hμ hmin hv)

theorem vector_mean_direction_covariance_integral_bound_341 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1)
    (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s) :
    vectorMeanDirectionCovarianceIntegral (n:=n) μ s β t s ht.le≤
      341*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*s) := by
  let M : ℝ:=(n:ℝ)*((1-t)*β^2)
  let B : ℝ:=341*(1+logPlus M)^2/M
  have hM : 0<M:=mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hB : 0≤B:=by dsimp [B];positivity
  have hm:=measurable_vectorMeanDirectionCovariance (n:=n) μ β t s hβ ht
  have hi:=integrable_vectorMeanDirectionCovariance hn μ s β t s hβ ht
  have hi' : Integrable (fun v=>vectorMeanDirectionCovariance (n:=n) μ β t s ht.le
      (parisiFreeQuantile μ s v)) (volume.restrict (Ioc (0:ℝ) (1-s))) := by
    rw [←parisiFreeQuantile_map μ s] at hi
    exact (integrable_map_measure hm.aestronglyMeasurable
      (parisiFreeQuantile_measurable μ s).aemeasurable).mp hi
  have hnv (v : ℝ) (hv : v∈Icc (0:ℝ) (1-s)) : (s+v)^2≠0:=
    pow_ne_zero 2 (ne_of_gt (by linarith [hs.1,hv.1]))
  have hc : ContinuousOn (fun v : ℝ=>1/(s+v)^2) (Icc 0 (1-s)) := by
    fun_prop (disch := intro v hv; exact hnv v hv)
  have hj : IntegrableOn (fun v : ℝ=>1/(s+v)^2) (Ioc 0 (1-s)) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  unfold vectorMeanDirectionCovarianceIntegral
  rw [integral_parisiFreeMeasure μ s _ hm]
  calc
    _≤∫v in Ioc (0:ℝ) (1-s),B*(1/(s+v)^2) := by
      apply integral_mono_ae hi' (hj.const_mul B)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have h:=vector_mean_direction_covariance_bound_341 hn μ s β t hβ ht hs hμ hmin hv
      convert h using 1
      dsimp [B,M]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _=B*(s⁻¹-1) := by rw [integral_const_mul,integral_inverse_square_shift s ⟨hs.1,hs.2.le⟩]
    _≤B*s⁻¹ := mul_le_mul_of_nonneg_left (by linarith) hB
    _=341*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*s) := by
      dsimp [B,M]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

theorem mean_direction_covariance_341 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2))
    (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s) :
    (∀v∈Ioo (0:ℝ) (1-s),
      vectorMeanDirectionCovariance (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)≤
        341*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*(s+v)^2)) ∧
    vectorMeanDirectionCovarianceIntegral (n:=n) μ s β t s ht.le≤
      341*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*s) := by
  have hs' : s∈Ioo (0:ℝ) 1:=⟨hs.1,by linarith [hs.2]⟩
  exact ⟨fun v hv=>vector_mean_direction_covariance_bound_341 hn μ s β t hβ ht hs' hμ hmin ⟨hv.1,hv.2.le⟩,
    vector_mean_direction_covariance_integral_bound_341 hn μ s β t hβ ht hs' hμ hmin⟩

end HexagonPaper
