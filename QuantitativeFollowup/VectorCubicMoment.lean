module
public import QuantitativeFollowup.VectorCubicLayercake
public import QuantitativeFollowup.VectorIntegratedTailRegularity

@[expose] public section

/-! Corollary 3.3 at the literal actual-model scope and exact constant 425.
All tail, contact, kernel, variance and layer-cake estimates are discharged. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_cubic_self_overlap_moment (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2)) (z : ℝ) (hz : z∈Ioc (0:ℝ) (1/4)) :
    vectorIntegratedSelfOverlapCubic (n:=n) μ s β t ht.le≤
      z*vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le+
      (425/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))*Real.log (2/z) :=by
  let M:=(n:ℝ)*((1-t)*β^2)
  let A:=170*(1/(M*s))*Real.log (2*M)
  let T:=vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht.le
  have hMp : 0<M:=zero_lt_one.trans_le hM
  have hA : 0≤A:=mul_nonneg
    (mul_nonneg (by norm_num) (one_div_pos.mpr (mul_pos hMp hs.1)).le)
    (Real.log_nonneg (by linarith))
  have hiT:=integrableOn_vectorIntegratedSelfOverlapSquareTail hn μ s β t ht.le z (1/4)
  have hRec : ContinuousOn (fun θ : ℝ=>A/θ) (Icc z (1/4)):=
    continuousOn_const.div continuousOn_id (fun θ hθ=>ne_of_gt (hz.1.trans_le hθ.1))
  have hiRec : IntervalIntegrable (fun θ : ℝ=>A/θ) volume z (1/4):=
    hRec.intervalIntegrable_of_Icc hz.2
  have hiRec' : IntegrableOn (fun θ : ℝ=>A/θ) (Ioo z (1/4)):=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hz.2).mp hiRec
  have hm:=integral_mono_ae hiT hiRec' (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact vector_quantile_total_square_tail hn μ s β t hβ ht hs hμ hmin hM θ
      ⟨hz.1.trans hθ.1,hθ.2.le⟩)
  have hVal : (∫θ in Ioo z (1/4),A/θ)=A*Real.log ((1/4)/z):=by
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hz.2]
    calc
      _=(∫θ in z..(1/4),A*(1/θ)):=by congr 1;funext θ;ring
      _=A*Real.log ((1/4)/z):=by rw [intervalIntegral.integral_const_mul,
        integral_one_div_of_pos hz.1 (by norm_num)]
  rw [hVal] at hm
  have hlog:=Real.log_le_log (div_pos (by norm_num : (0:ℝ)<1/4) hz.1)
    (div_le_div_of_nonneg_right (by norm_num : (1/4:ℝ)≤2) hz.1.le)
  have hm' : (∫θ in Ioo z (1/4),T θ)≤A*Real.log (2/z):=
    hm.trans (mul_le_mul_of_nonneg_left hlog hA)
  have hq:=vector_quantile_total_square_tail hn μ s β t hβ ht hs hμ hmin hM (1/4)
    ⟨by norm_num,le_rfl⟩
  have hq' : T (1/4)≤4*A:=by
    change T (1/4)≤A/(1/4) at hq
    convert hq using 1 <;> ring
  have he:=vector_cubic_truncated_layercake hn μ s β t hβ ht hs hμ hmin z hz
  have hL:=two_le_log_two_div hz.1 hz.2
  have hAL:=mul_le_mul_of_nonneg_left hL hA
  have he' : vectorIntegratedSelfOverlapCubic (n:=n) μ s β t ht.le≤
      z*vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le+(5/2)*A*Real.log (2/z):=by
    change _≤z*vectorIntegratedSelfOverlapVariance μ s β t ht.le+
      (∫θ in Ioo z (1/4),T θ)+(3/4)*T (1/4) at he
    nlinarith
  convert he' using 1 <;> dsimp only [A,M] <;> ring

end QuantitativeFollowup
