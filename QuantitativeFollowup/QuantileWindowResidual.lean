module
public import QuantitativeFollowup.QuantileWindowAveraging
public import QuantitativeFollowup.ParisiFreeQuantileSupport
public import QuantitativeFollowup.MeanCovarianceResidual

@[expose] public section

/-! The literal residual bound throughout the padded earlier-quantile
window, including its negative-level part and arbitrary overlap atoms. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem logPlus_le_of_nonneg_le {z Z : ℝ} (hz : 0≤z) (h : z≤Z) : logPlus z≤logPlus Z := by
  by_cases hp : 0<z
  · exact max_le_max (Real.log_le_log hp h) le_rfl
  · have hz0 : z=0:=le_antisymm (not_lt.mp hp) hz
    rw [hz0,logPlus,Real.log_zero,max_self]
    exact logPlus_nonneg Z

theorem parisiPaddedFreeQuantile_le (μ : Paper.ParisiMeasure) (s v w : ℝ)
    (hv : 0<v) (hw : w≤v) : parisiPaddedFreeQuantile μ s w≤parisiFreeQuantile μ s v := by
  have h:=parisiPaddedFreeQuantile_monotone μ s hw
  simpa only [parisiPaddedFreeQuantile,ite_eq_right (not_le.mpr hv)] using h

theorem parisiPaddedFreeQuantile_mid_cdf_lower (μ : Paper.ParisiMeasure) (s v w : ℝ)
    (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hv : v∈Ioc (0:ℝ) (1-s))
    (hw : w∈Ioc (v-(s+v)/2) v) :
    (s+v)/2≤Paper.parisiCDF μ
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
    change (s+v)/2≤Paper.parisiCDF μ (dyadicOverlap p q hpq 1)
    linarith [hw.1]
  · have hwpos : 0<w:=lt_of_not_ge hw0
    have hp : p=parisiFreeQuantile μ s w := by simp only [p,parisiPaddedFreeQuantile,ite_eq_right hw0]
    have hc:=parisiCDF_freeQuantile_lower μ s ⟨hs.1.le,hs.2⟩ ⟨hwpos,hw.2.trans hv.2⟩
    have hm:=Paper.parisiCDF_monotone μ hpm
    have hcp : s+w≤Paper.parisiCDF μ p:=by simpa only [hp] using hc
    change (s+v)/2≤Paper.parisiCDF μ (dyadicOverlap p q hpq 1)
    linarith [hw.1]

theorem vector_quantile_window_residual_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hv : v∈Ioc (0:ℝ) (1-s)) (w : ℝ) (hw : w∈Ioc (v-(s+v)/2) v) :
    vectorMeanCovarianceIncrement (n:=n) μ β t s ht.le
      (parisiPaddedFreeQuantile μ s w) (parisiFreeQuantile μ s v)≤
      224*(1+logPlus ((n:ℝ)*((1-t)*β^2)))^2/((n:ℝ)*((1-t)*β^2)*(s+v)^2) := by
  let p:=parisiPaddedFreeQuantile μ s w
  let q:=parisiFreeQuantile μ s v
  let M:=(n:ℝ)*((1-t)*β^2)
  let x:=(s+v)/2
  have hpq:p≤q:=parisiPaddedFreeQuantile_le μ s v w hv.1 hw.2
  have hM : 0<M:=mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hx : 0<x:=by dsimp only [x];linarith [hs.1,hv.1]
  have hA:=parisiPaddedFreeQuantile_mid_cdf_lower μ s v w hs hμ hv hw
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
    _=224*(1+logPlus M)^2/(M*(s+v)^2) := by
      dsimp only [x]
      field_simp
      ring

end QuantitativeFollowup
