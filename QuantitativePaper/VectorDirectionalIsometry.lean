module
public import QuantitativePaper.VectorDirectionalStochastic

@[expose] public section

/-! The genuine weighted directional Itô isometry of the physical spin-mean
martingale. The direction may be any bounded vector measurable in the earlier
whole Wiener/disorder past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorDirectionEnergy (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (b : VectorDisorderBrownianSample n→Field n) (q : Paper.Overlap) : ℝ :=
  ∫sample,‖vectorMeasureHessianProcess μ β t ht q sample (b sample)‖^2∂vectorMeasureDisorderTilt μ β t a

theorem measurable_vectorDirectionEnergy_integrand (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (b : VectorDisorderBrownianSample n→Field n) (hb : Measurable b) (q : Paper.Overlap) :
    Measurable (fun sample=>‖vectorMeasureHessianProcess μ β t ht q sample (b sample)‖^2) := by
  have hH := (adapted_vectorMeasureHessianProcess μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl
  exact (((continuous_fst.clm_apply continuous_snd).measurable.comp (hH.prodMk hb)).norm.pow_const 2)

theorem vectorDirectionEnergy_integrand_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (b : VectorDisorderBrownianSample n→Field n) (K : ℝ≥0)
    (hK : ∀sample,‖b sample‖≤K) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureHessianProcess μ β t ht q sample (b sample)‖^2≤((n:ℝ)*K)^2 := by
  have h := ((vectorMeasureHessianProcess μ β t ht q sample).le_opNorm _).trans
    (mul_le_mul (norm_vectorMeasureHessianProcess_le μ β t ht q sample) (hK sample)
      (norm_nonneg _) (Nat.cast_nonneg n))
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem continuous_vectorDirectionEnergy (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (b : VectorDisorderBrownianSample n→Field n) (hb : Measurable b) (K : ℝ≥0)
    (hK : ∀sample,‖b sample‖≤K) : Continuous (vectorDirectionEnergy μ β t a ht b) := by
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply continuous_of_dominated (μ:=vectorMeasureDisorderTilt μ β t a) (bound:=fun _=>((n:ℝ)*K)^2)
  · intro q
    exact (measurable_vectorDirectionEnergy_integrand μ β t ht b hb q).aestronglyMeasurable
  · intro q
    exact .of_forall fun sample=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact vectorDirectionEnergy_integrand_bound μ β t ht b K hK q sample
  · exact integrable_const _
  · exact .of_forall fun sample=>
      (((continuous_vectorMeasureHessianProcess_path μ β t ht sample).clm_apply continuous_const).norm.pow 2)

theorem vectorMeanBrownian_row_energy (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (b : Field n) :
    (∑j : Fin n,(((InnerProductSpace.toDual ℝ (Field n)) b).comp
      (vectorMeanBrownianIntegrand μ β t ht q sample) (EuclideanSpace.single j 1))^2)=
      ((1-t)*β^2)*‖vectorMeasureHessianProcess μ β t ht q sample b‖^2 := by
  simp only [ContinuousLinearMap.comp_apply,InnerProductSpace.toDual_apply_apply,
    vectorMeanBrownianIntegrand,smul_apply,real_inner_smul_right,mul_pow]
  simp_rw [vectorMeasureHessianProcess_inner_basis]
  rw [Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)),←Finset.mul_sum,
    EuclideanSpace.real_norm_sq_eq]

def vectorMeanDirectionRow (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (b : VectorDisorderBrownianSample n→Field n) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) : Field n→L[ℝ]ℝ :=
  ((InnerProductSpace.toDual ℝ (Field n)) (b sample)).comp
    (vectorMeanBrownianIntegrand μ β t ht q sample)

theorem adapted_vectorMeanDirectionRow (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (b : VectorDisorderBrownianSample n→Field n) (q : Paper.Overlap)
    (hb : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] b) :
    Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] (vectorMeanDirectionRow μ β t ht b q) := by
  have hc : Continuous (fun p : (Field n→L[ℝ]ℝ)×(Field n→L[ℝ]Field n)=>p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  exact hc.measurable.comp
    (((InnerProductSpace.toDual ℝ (Field n)).continuous.measurable.comp hb).prodMk
      (adapted_vectorMeanBrownianIntegrand μ β t ht q))

theorem norm_vectorMeanDirectionRow_le (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (b : VectorDisorderBrownianSample n→Field n) (K : ℝ≥0) (hK : ∀sample,‖b sample‖≤K)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeanDirectionRow μ β t ht b q sample‖≤K*Real.sqrt ((1-t)*β^2)*(n:ℝ) := by
  apply (((InnerProductSpace.toDual ℝ (Field n)) (b sample)).opNorm_comp_le _).trans
  rw [(InnerProductSpace.toDual ℝ (Field n)).norm_map]
  exact (mul_le_mul (hK sample) (norm_vectorMeanBrownianIntegrand_le μ β t ht q sample)
    (norm_nonneg _) K.coe_nonneg).trans_eq (by ring)

theorem vectorMeanLeftSum_direction_eq_rowSum (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) (b : VectorDisorderBrownianSample n→Field n)
    (sample : VectorDisorderBrownianSample n) :
    inner ℝ (b sample) (vectorMeanLeftSum μ β t ht r q hrq N sample)=
      vectorBrownianLinearSum (fun i=>(vectorUniformOverlapGrid r q hrq N i:ℝ).toNNReal)
        (fun i=>vectorMeanDirectionRow μ β t ht b (vectorUniformOverlapGrid r q hrq N i.castSucc)) sample := by
  change ((InnerProductSpace.toDual ℝ (Field n)) (b sample)) (∑i : Fin (N+1),_) = _
  rw [map_sum]
  rfl

theorem vectorMeanLeftSum_direction_secondMoment (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (K : ℝ≥0) (hK : ∀sample,‖b sample‖≤K) :
    (∫sample,(inner ℝ (b sample) (vectorMeanLeftSum μ β t ht r q hrq N sample))^2∂vectorMeasureDisorderTilt μ β t a)=
      ∑i : Fin (N+1),((1-t)*β^2)*vectorDirectionEnergy μ β t a ht b
        (vectorUniformOverlapGrid r q hrq N i.castSucc)*
        ((vectorUniformOverlapGrid r q hrq N i.succ:ℝ)-vectorUniformOverlapGrid r q hrq N i.castSucc) := by
  let T := vectorUniformOverlapGrid r q hrq N
  have hT : Monotone T := monotone_vectorUniformOverlapGrid r q hrq N
  have hbT (i : Fin (N+1)) : Measurable[vectorBrownianFiltration n (T i.castSucc:ℝ).toNNReal] b := by
    apply hb.mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono ?_)) le_rfl
    have hh : r≤T i.castSucc := by
      simpa only [T,vectorUniformOverlapGrid_zero] using hT (Fin.zero_le i.castSucc)
    exact hh
  let B := (K*Real.sqrt ((1-t)*β^2)*(n:ℝ)).toNNReal
  simp_rw [vectorMeanLeftSum_direction_eq_rowSum]
  rw [integral_vectorBrownianLinearSum_square μ β t a ht _
    (fun i j hij=>Real.toNNReal_mono (hT hij)) _
    (fun i=>adapted_vectorMeanDirectionRow μ β t ht b (T i.castSucc) (hbT i)) B
    (fun i sample=>by
      rw [Real.coe_toNNReal _ (by positivity : 0≤(K:ℝ)*Real.sqrt ((1-t)*β^2)*(n:ℝ))]
      exact norm_vectorMeanDirectionRow_le μ β t ht b K hK _ sample)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [vectorMeanDirectionRow,vectorMeanBrownian_row_energy]
  rw [integral_const_mul,Real.coe_toNNReal _ (T i.succ).property.1,
    Real.coe_toNNReal _ (T i.castSucc).property.1]
  dsimp only [vectorDirectionEnergy,T]
  ring

theorem vectorMean_direction_increment_isometry (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (K : ℝ≥0) (hK : ∀sample,‖b sample‖≤K) :
    (∫sample,(inner ℝ (b sample) (vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample))^2
      ∂vectorMeasureDisorderTilt μ β t a)=
      ((1-t)*β^2)*∫s in (r:ℝ)..(q:ℝ),vectorDirectionEnergy μ β t a ht.le b (projIcc 0 1 zero_le_one s) := by
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  have hbm : Measurable b := hb.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hU := memLp_inner_bounded_left b _ hbm
    ((memLp_vectorMeasureSpinMean μ β t a ht.le q).sub (memLp_vectorMeasureSpinMean μ β t a ht.le r)) K hK
  have hX (N : ℕ) := memLp_inner_bounded_left b _ hbm (memLp_vectorMeanLeftSum μ β t a ht.le r q hrq N) K hK
  have hlim := tendsto_integral_norm_sq_of_meanSquare hX hU
    (tendsto_vectorMeanLeftSum_direction_L2 hn μ β t a hβ ht r q hrq b hbm K hK)
  have hf : Continuous (fun s : ℝ=>((1-t)*β^2)*vectorDirectionEnergy μ β t a ht.le b (projIcc 0 1 zero_le_one s)) :=
    ((continuous_vectorDirectionEnergy μ β t a ht.le b hbm K hK).comp continuous_projIcc).const_mul _
  have hR := vectorUniformOverlapGrid_riemann_tendsto r q hrq _ hf
  have hR' : Tendsto (fun N=>∫sample,(inner ℝ (b sample) (vectorMeanLeftSum μ β t ht.le r q hrq N sample))^2
      ∂vectorMeasureDisorderTilt μ β t a) atTop
      (𝓝 (((1-t)*β^2)*∫s in (r:ℝ)..(q:ℝ),vectorDirectionEnergy μ β t a ht.le b (projIcc 0 1 zero_le_one s))) := by
    simp_rw [vectorMeanLeftSum_direction_secondMoment μ β t a ht.le r q hrq _ b hb K hK]
    simpa only [projIcc_val,intervalIntegral.integral_const_mul] using hR
  have hlim' := hlim
  simp only [Real.norm_eq_abs,sq_abs] at hlim'
  exact tendsto_nhds_unique hlim' hR'

end QuantitativePaper
