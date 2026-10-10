module
public import HexagonPaper.MomentsCubicActualLayercake
public import HexagonPaper.MomentsCubicTail
public import QuantitativeFollowup.VectorIntegratedTailRegularity

@[expose] public section

/-! The revised full layer-cake proof gives the manuscript's stronger literal
170 bound, before its unchanged 425 corollary. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace HexagonPaper
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

/-- Display 085, first inequality: the genuine actual-model cubic bound. -/
theorem vector_cubic_self_overlap_moment_170_log_one (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2)) (z : ℝ) (hz : z∈Ioc (0:ℝ) 1) :
    vectorIntegratedSelfOverlapCubic (n:=n) μ s β t ht.le≤
      z*vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le+
      (170/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))*Real.log (1/z) :=by
  let M:=(n:ℝ)*((1-t)*β^2)
  let A:=170*(1/(M*s))*Real.log (2*M)
  let T:=vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht.le
  have hiT:=integrableOn_vectorIntegratedSelfOverlapSquareTail hn μ s β t ht.le z 1
  have hRec : ContinuousOn (fun θ : ℝ=>A/θ) (Icc z 1):=
    continuousOn_const.div continuousOn_id (fun θ hθ=>ne_of_gt (hz.1.trans_le hθ.1))
  have hiRec : IntervalIntegrable (fun θ : ℝ=>A/θ) volume z 1:=
    hRec.intervalIntegrable_of_Icc hz.2
  have hiRec' : IntegrableOn (fun θ : ℝ=>A/θ) (Ioo z 1):=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hz.2).mp hiRec
  have hm:=integral_mono_ae hiT hiRec' (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact vector_quantile_total_square_tail_to_one hn μ s β t hβ ht hs hμ hmin hM θ
      ⟨hz.1.trans hθ.1,hθ.2.le⟩)
  have hVal : (∫θ in Ioo z 1,A/θ)=A*Real.log (1/z):=by
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hz.2]
    calc
      _=(∫θ in z..1,A*(1/θ)):=by congr 1;funext θ;ring
      _=A*Real.log (1/z):=by rw [intervalIntegral.integral_const_mul,
        integral_one_div_of_pos hz.1 zero_lt_one]
  rw [hVal] at hm
  have he:=vector_cubic_full_layercake hn μ s β t hβ ht hs hμ hmin z hz
  have hAeq : A=(170/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2))) :=by
    dsimp only [A,M]
    ring
  rw [hAeq] at hm
  exact he.trans (add_le_add le_rfl hm)

/-- Display 085, second inequality: the stronger coefficient 170. -/
theorem vector_cubic_self_overlap_moment_170 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2)) (z : ℝ) (hz : z∈Ioc (0:ℝ) 1) :
    vectorIntegratedSelfOverlapCubic (n:=n) μ s β t ht.le≤
      z*vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le+
      (170/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))*Real.log (2/z) :=by
  have he:=vector_cubic_self_overlap_moment_170_log_one hn μ s β t hβ ht hs hμ hmin hM z hz
  apply he.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left
  · exact Real.log_le_log (one_div_pos.mpr hz.1)
      (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤2) hz.1.le)
  · apply mul_nonneg
      (div_nonneg (by norm_num) (mul_pos (zero_lt_one.trans_le hM) hs.1).le)
    exact Real.log_nonneg (by linarith)

/-- The printed Corollary 3.3 follows from the revised stronger proof. -/
theorem vector_cubic_self_overlap_moment_425_from_full_layercake (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hβ : β≠0) (ht : t<1)
    (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2)) (z : ℝ) (hz : z∈Ioc (0:ℝ) (1/4)) :
    vectorIntegratedSelfOverlapCubic (n:=n) μ s β t ht.le≤
      z*vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le+
      (425/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))*Real.log (2/z) :=by
  have he:=vector_cubic_self_overlap_moment_170 hn μ s β t hβ ht hs hμ hmin hM z
    ⟨hz.1,by linarith [hz.2]⟩
  apply he.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact div_le_div_of_nonneg_right (by norm_num : (170:ℝ)≤425)
        (mul_pos (zero_lt_one.trans_le hM) hs.1).le
    · exact Real.log_nonneg (by linarith)
  · exact Real.log_nonneg (by
      apply (le_div_iff₀ hz.1).mpr
      linarith [hz.2])

end HexagonPaper
