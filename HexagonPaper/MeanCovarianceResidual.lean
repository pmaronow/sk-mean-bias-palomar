module
public import QuantitativeFollowup.QuantileWindowResidualAverage

@[expose] public section

/-! A smaller earlier window improves the actual mean-direction residual budget. -/
noncomputable section
open Set MeasureTheory QuantitativePaper QuantitativeFollowup
open scoped NNReal ENNReal
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem quarter_window_mid_cdf_lower (μ : Paper.ParisiMeasure) (s v w : ℝ)
    (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hv : v∈Ioc (0:ℝ) (1-s))
    (hw : w∈Ioc (v-(s+v)/4) v) :
    3*(s+v)/4≤Paper.parisiCDF μ
      (dyadicOverlap (parisiPaddedFreeQuantile μ s w) (parisiFreeQuantile μ s v)
        (parisiPaddedFreeQuantile_le μ s v w hv.1 hw.2) 1) := by
  let p:=parisiPaddedFreeQuantile μ s w
  let q:=parisiFreeQuantile μ s v
  have hpq:p≤q:=parisiPaddedFreeQuantile_le μ s v w hv.1 hw.2
  have hpm : p≤dyadicOverlap p q hpq 1 := by
    simpa only [dyadicOverlap_zero] using monotone_dyadicOverlap p q hpq (Nat.zero_le 1)
  by_cases hw0 : w≤0
  · have hsf: s≤Paper.parisiCDF μ (dyadicOverlap p q hpq 1):=
      scalarFloor_cdf_lower hμ (dyadicOverlap p q hpq 1).property.1
    change 3*(s+v)/4≤Paper.parisiCDF μ (dyadicOverlap p q hpq 1)
    linarith [hw.1]
  · have hwpos : 0<w:=lt_of_not_ge hw0
    have hp : p=parisiFreeQuantile μ s w := by simp only [p,parisiPaddedFreeQuantile,ite_eq_right hw0]
    have hc:=parisiCDF_freeQuantile_lower μ s ⟨hs.1.le,hs.2⟩ ⟨hwpos,hw.2.trans hv.2⟩
    have hm:=Paper.parisiCDF_monotone μ hpm
    have hcp : s+w≤Paper.parisiCDF μ p:=by simpa only [hp] using hc
    change 3*(s+v)/4≤Paper.parisiCDF μ (dyadicOverlap p q hpq 1)
    linarith [hw.1]

theorem vector_quarter_window_residual_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hv : v∈Ioc (0:ℝ) (1-s)) (w : ℝ) (hw : w∈Ioc (v-(s+v)/4) v) :
    vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le
      (parisiPaddedFreeQuantile μ s w) (parisiFreeQuantile μ s v)≤
      100*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*(s+v)^2) := by
  let p:=parisiPaddedFreeQuantile μ s w
  let q:=parisiFreeQuantile μ s v
  let M:=(n:ℝ)*((1-t)*β^2)
  let x:=3*(s+v)/4
  have hpq:p≤q:=parisiPaddedFreeQuantile_le μ s v w hv.1 hw.2
  have hM : 0<M:=mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hx : 0<x:=by dsimp only [x];linarith [hs.1,hv.1]
  have hA:=quarter_window_mid_cdf_lower μ s v w hs hμ hv hw
  have hd : 0≤(q:ℝ)-p:=sub_nonneg.mpr hpq
  have hd1 : (q:ℝ)-p≤1:=by linarith [q.property.2,p.property.1]
  have hlog : logPlus (M*((q:ℝ)-p))≤logPlus M :=
    logPlus_le_of_nonneg_le (mul_nonneg hM.le hd)
      ((mul_le_mul_of_nonneg_left hd1 hM.le).trans_eq (mul_one M))
  have hpow : (1+logPlus (M*((q:ℝ)-p)))^2≤(1+logPlus M)^2 :=
    pow_le_pow_left₀ (by linarith [logPlus_nonneg (M*((q:ℝ)-p))]) (add_le_add le_rfl hlog) 2
  have hden : 0<M*x^2:=mul_pos hM (sq_pos_of_pos hx)
  have hdenA : M*x^2≤M*(Paper.parisiCDF μ (dyadicOverlap p q hpq 1))^2 := by
    apply mul_le_mul_of_nonneg_left _ hM.le
    exact pow_le_pow_left₀ hx.le hA 2
  have hbase:=vector_mean_covariance_residual_bound hn μ s hs hμ β t s hβ ht hs.1.le hmin p q hpq
    (parisiFreeQuantile_mem_support μ s ⟨hs.1.le,hs.2⟩ hv)
  apply hbase.trans
  calc
    _≤56*(1+logPlus M)^2/(M*x^2) := by
      apply div_le_div₀ (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hpow (by norm_num)) hden hdenA
    _=(896/9)*(1+logPlus M)^2/(M*(s+v)^2) := by
      dsimp only [x]
      field_simp
      ring
    _≤100*(1+logPlus M)^2/(M*(s+v)^2) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hM.le (sq_nonneg _))
      exact mul_le_mul_of_nonneg_right (by norm_num : (896/9:ℝ)≤100) (sq_nonneg _)

theorem vector_quarter_window_residual_average_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hv : v∈Ioc (0:ℝ) (1-s)) :
    (∫w,vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le
      (parisiPaddedFreeQuantile μ s w) (parisiFreeQuantile μ s v)
      ∂quantileWindowAveraging v ((s+v)/4))≤
        100*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*(s+v)^2) := by
  have hx : 0<(s+v)/4:=by linarith [hs.1,hv.1]
  let :=quantileWindowAveraging_probability v ((s+v)/4) hx
  have hi:=integrable_quantileWindowMeanCovarianceIncrement (n:=n) μ s β t s v ((s+v)/4) ht.le hx
    (parisiFreeQuantile μ s v)
  have ha : ∀ᵐw ∂quantileWindowAveraging v ((s+v)/4),w∈Ioc (v-(s+v)/4) v :=
    Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
  have h:=integral_mono_ae hi (integrable_const
    (100*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*(s+v)^2)))
    (ha.mono fun w hw=>vector_quarter_window_residual_bound hn μ s β t v hβ ht hs hμ hmin hv w hw)
  simpa only [integral_const,probReal_univ,one_smul] using h

end HexagonPaper
