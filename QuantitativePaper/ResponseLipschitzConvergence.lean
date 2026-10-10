module
public import QuantitativePaper.ResponseLipschitzFunctionals
public import QuantitativePaper.ResponseBounds
public import QuantitativePaper.VectorDyadicUniformResponse
public import FourPapersCommon.UniformWeakIntegral
public import FRSB.ParisiMeasureTopology

@[expose] public section

/-! Genuine time and Stieltjes convergence of the actual response
integrals along the common dyadic probability-measure approximations. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem tendstoUniformly_response_Lipschitz_curvature_grid (μ : Paper.ParisiMeasure)
    (β t lam : ℝ) (ht : t≤1) (w : ResponseLipschitzTest) :
    TendstoUniformly (fun j (q : Paper.Overlap)=>(w.value q)^2*
      responseAveragedCurvature (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t lam ht q)
      (fun q=>(w.value q)^2*responseAveragedCurvature (n:=n) μ β t lam ht q) atTop:=by
  let f : Paper.Overlap →ᵇ ℝ:=BoundedContinuousFunction.mkOfCompact
    ⟨fun q=>w.value q,w.continuous.comp continuous_subtype_val⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let δ:=ε/(‖f‖^2+1)
  have hδ : 0<δ:=by dsimp [δ];positivity
  filter_upwards [(Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_responseAveragedCurvature_grid (n:=n) μ β t lam ht)) δ hδ] with j hj
  intro q
  rw [dist_eq_norm,←mul_sub,norm_mul]
  rw [norm_sub_rev (responseAveragedCurvature (n:=n) μ β t lam ht q)]
  have hb : ‖(w.value q)^2‖≤‖f‖^2:=by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm q) 2
  have hd : ‖responseAveragedCurvature (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t lam ht q-
      responseAveragedCurvature (n:=n) μ β t lam ht q‖≤δ:=by
    simpa only [dist_eq_norm,norm_sub_rev] using (hj q).le
  apply (mul_le_mul hb hd (norm_nonneg _) (sq_nonneg _)).trans_lt
  dsimp [δ]
  rw [←mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : 0<‖f‖^2+1)).mpr
  nlinarith

theorem tendsto_integral_response_Lipschitz_curvature_grid (μ : Paper.ParisiMeasure)
    (β t lam : ℝ) (ht : t<1) (w : ResponseLipschitzTest) :
    Tendsto (fun j=>∫q : Paper.Overlap,(w.value q)^2*
      responseAveragedCurvature (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t lam ht.le q
      ∂(Paper.parisiGridMeasure μ (vectorDyadicIndex j):Measure Paper.Overlap)) atTop
      (nhds (∫q : Paper.Overlap,(w.value q)^2*responseAveragedCurvature (n:=n) μ β t lam ht.le q
        ∂(μ:Measure Paper.Overlap))):=by
  exact tendsto_integral_of_uniform_and_weak _ μ
    ((FRSB.tendsto_parisiGridMeasure μ).comp tendsto_vectorDyadicIndex) _ _
    (fun j=>(w.continuous.comp continuous_subtype_val).pow 2 |>.mul
      (continuous_responseAveragedCurvature _ β t lam ht))
    ((w.continuous.comp continuous_subtype_val).pow 2 |>.mul
      (continuous_responseAveragedCurvature μ β t lam ht))
    (tendstoUniformly_response_Lipschitz_curvature_grid μ β t lam ht.le w)

theorem tendsto_integral_response_Lipschitz_mean_grid (μ : Paper.ParisiMeasure)
    (β t lam : ℝ) (ht : t≤1) (w : ResponseLipschitzTest) :
    Tendsto (fun j=>∫q in (0:ℝ)..1,(w.slope q)^2*
      responseMeanHessianReal (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t lam ht q)
      atTop (nhds (∫q in (0:ℝ)..1,(w.slope q)^2*responseMeanHessianReal (n:=n) μ β t lam ht q)):=by
  let τ : Measure ℝ:=volume.restrict (Ioc (0:ℝ) 1)
  letI : IsFiniteMeasure τ:=isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  let C:=|1/(n:ℝ)| *(|β| *(n:ℝ)^2)
  have hlim:=tendsto_integral_of_dominated_convergence (μ:=τ)
    (F:=fun j q=>(w.slope q)^2*responseMeanHessianReal (n:=n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t lam ht q)
    (f:=fun q=>(w.slope q)^2*responseMeanHessianReal (n:=n) μ β t lam ht q)
    (fun _=>(w.lipschitzBound:ℝ)^2*C)
    (fun j=>((w.measurable_slope.pow_const 2).mul
      (continuous_responseMeanHessianReal (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        β t lam ht).measurable).aestronglyMeasurable)
    (integrable_const _) (fun j=>?_ ) (Eventually.of_forall fun q=>?_) 
  · simpa only [τ,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hlim
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    rw [norm_mul,norm_pow]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (norm_nonneg _) (w.slope_bound q) 2
    · exact norm_responseMeanHessian_le _ β t lam ht _
    · exact norm_nonneg _
    · exact sq_nonneg _
  · exact tendsto_const_nhds.mul
      ((tendstoUniformly_responseMeanHessian_grid (n:=n) μ β t lam ht).tendsto_at
        (projIcc 0 1 zero_le_one q))

theorem tendsto_integral_response_Lipschitz_signal_grid (μ ν ρ : Paper.ParisiMeasure)
    (β t lam : ℝ) (ht : t<1) (w : ResponseLipschitzTest) :
    Tendsto (fun j=>∫q in (0:ℝ)..1,
      β*(Paper.parisiCDF (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) q-
        Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) q)*w.value q*
        responseAveragedCurvatureReal (n:=n) (Paper.parisiGridMeasure ρ (vectorDyadicIndex j)) β t lam ht.le q)
      atTop (nhds (∫q in (0:ℝ)..1,β*(Paper.parisiCDF ν q-Paper.parisiCDF μ q)*w.value q*
        responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le q)):=by
  let τ : Measure ℝ:=volume.restrict (Ioc (0:ℝ) 1)
  letI : IsFiniteMeasure τ:=isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  let f : Paper.Overlap →ᵇ ℝ:=BoundedContinuousFunction.mkOfCompact
    ⟨fun q=>w.value q,w.continuous.comp continuous_subtype_val⟩
  let C:=|β^2/(n:ℝ)| *(n:ℝ)^3
  have hlim:=tendsto_integral_of_dominated_convergence (μ:=τ)
    (F:=fun j q=>β*(Paper.parisiCDF (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) q-
      Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) q)*w.value q*
      responseAveragedCurvatureReal (n:=n) (Paper.parisiGridMeasure ρ (vectorDyadicIndex j)) β t lam ht.le q)
    (f:=fun q=>β*(Paper.parisiCDF ν q-Paper.parisiCDF μ q)*w.value q*
      responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le q)
    (fun _=>|β| *‖f‖*C)
    (fun j=>((((Paper.parisiCDF_measurable (Paper.parisiGridMeasure ν (vectorDyadicIndex j))).sub
      (Paper.parisiCDF_measurable (Paper.parisiGridMeasure μ (vectorDyadicIndex j)))).const_mul β).mul
      w.continuous.measurable |>.mul
      (continuous_responseAveragedCurvatureReal (n:=n) (Paper.parisiGridMeasure ρ (vectorDyadicIndex j))
        β t lam ht).measurable).aestronglyMeasurable)
    (integrable_const _) (fun j=>?_) ?_
  · simpa only [τ,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hlim
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    have hq01 : q∈Icc (0:ℝ) 1:=⟨hq.1.le,hq.2⟩
    have hCDF : ‖Paper.parisiCDF (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) q-
        Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) q‖≤1:=by
      rw [Real.norm_eq_abs,abs_le]
      constructor <;>linarith [Paper.parisiCDF_nonneg (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) q,
        Paper.parisiCDF_nonneg (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) q,
        Paper.parisiCDF_le_one (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) q,
        Paper.parisiCDF_le_one (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) q]
    simp only [norm_mul,Real.norm_eq_abs]
    have hw : |w.value q|≤‖f‖:=by
      simpa only [f,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
        Real.norm_eq_abs] using f.norm_coe_le_norm ⟨q,hq01⟩
    have hz:=norm_responseAveragedCurvature_le (n:=n) (Paper.parisiGridMeasure ρ (vectorDyadicIndex j))
      β t lam ht.le (projIcc 0 1 zero_le_one q)
    dsimp only [responseAveragedCurvatureReal] at hz ⊢
    have hbound:=mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hCDF) (abs_nonneg β))
        (by simpa only [Real.norm_eq_abs] using hw) (abs_nonneg _) (by positivity))
      (by simpa only [Real.norm_eq_abs] using hz) (abs_nonneg _) (by positivity)
    convert hbound using 1 <;> dsimp only [C] <;> ring
  · filter_upwards [(FRSB.ae_parisi_level_null μ).filter_mono (ae_mono Measure.restrict_le_self),
      (FRSB.ae_parisi_level_null ν).filter_mono (ae_mono Measure.restrict_le_self)] with q hμ hν
    have hμ':=FRSB.tendsto_parisiCDF_of_level_null
      ((FRSB.tendsto_parisiGridMeasure μ).comp tendsto_vectorDyadicIndex) hμ
    have hν':=FRSB.tendsto_parisiCDF_of_level_null
      ((FRSB.tendsto_parisiGridMeasure ν).comp tendsto_vectorDyadicIndex) hν
    exact ((tendsto_const_nhds.mul (hν'.sub hμ')).mul tendsto_const_nhds).mul
      ((tendstoUniformly_responseAveragedCurvature_grid (n:=n) ρ β t lam ht.le).tendsto_at
        (projIcc 0 1 zero_le_one q))

end QuantitativePaper
