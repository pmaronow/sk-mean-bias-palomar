module
public import QuantitativePaper.VectorMeanStochasticSums

@[expose] public section

/-! Quantitative cross convergence for the actual vector diffusion-gradient
Brownian sums on every physical interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem vectorMeanLeftSum_cross_sum_bound (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) :
    ‖(∫sample : VectorDisorderBrownianSample n,
      inner ℝ (vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample)
        (vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample)∂vectorMeasureDisorderTilt μ β t a)-
      (∫sample : VectorDisorderBrownianSample n,‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample‖^2∂vectorMeasureDisorderTilt μ β t a)‖≤
      vectorMeanCrossErrorConstant n β t*((q:ℝ)-r)*Real.sqrt (((q:ℝ)-r)/(N+1)) := by
  let T := vectorUniformOverlapGrid r q hrq N
  have hT : Monotone T := monotone_vectorUniformOverlapGrid r q hrq N
  let H := fun i : Fin (N+1) => vectorMeanBrownianIntegrand (n:=n) μ β t ht.le (T i.castSucc)
  let K := (Real.sqrt ((1-t)*β^2)*(n:ℝ)).toNNReal
  have hK (i : Fin (N+1)) (sample : VectorDisorderBrownianSample n) : ‖H i sample‖≤K := by
    rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n))]
    exact norm_vectorMeanBrownianIntegrand_le μ β t ht.le _ sample
  have hc := integral_vectorMatrixBrownianSum_cross_martingale μ β t a ht.le
    (vectorMeasureSpinMean μ β t ht.le)
    (fun l => QuantitativeFollowup.martingale_vectorMeasureSpinMean_component μ β t a hβ ht l)
    (fun q l => memLp_vectorMeasureSpinMean_component μ β t a ht.le q l) T hT H
    (fun i => adapted_vectorMeanBrownianIntegrand μ β t ht.le _) K hK
  have hc' : (∫sample : VectorDisorderBrownianSample n,
      inner ℝ (vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample)
        (vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample)∂vectorMeasureDisorderTilt μ β t a)=
      ∑i : Fin (N+1),∫sample : VectorDisorderBrownianSample n,inner ℝ
        (vectorMeasureSpinMean μ β t ht.le (T i.succ) sample-vectorMeasureSpinMean μ β t ht.le (T i.castSucc) sample)
        (H i sample (disorderVectorBrownianIncrement (T i.castSucc:ℝ).toNNReal (T i.succ:ℝ).toNNReal sample))
          ∂vectorMeasureDisorderTilt μ β t a := by
    simpa only [T,H,vectorUniformOverlapGrid_zero,vectorUniformOverlapGrid_last,vectorMeanLeftSum] using hc
  have hv (i : Fin (N+1)) : (∫sample : VectorDisorderBrownianSample n,
      ‖H i sample (disorderVectorBrownianIncrement (T i.castSucc:ℝ).toNNReal (T i.succ:ℝ).toNNReal sample)‖^2
        ∂vectorMeasureDisorderTilt μ β t a)=
      (n:ℝ)*vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (T i.castSucc)*((T i.succ:ℝ)-T i.castSucc) := by
    rw [integral_vectorMeanBrownianLocalTerm_norm_sq μ β t a ht.le _ _ (hT (Fin.castSucc_le_succ i))]
    unfold vectorMeanOverlapDerivative
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0:ℝ)<n)]
  rw [hc',vectorMeanLeftSum_secondMoment hn μ β t a ht.le r q hrq N]
  change ‖(∑i : Fin (N+1),_)-(∑i : Fin (N+1),(n:ℝ)*vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (T i.castSucc)*
    ((T i.succ:ℝ)-T i.castSucc))‖≤_
  simp_rw [←hv]
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (le_trans (b:=∑_i : Fin (N+1),vectorMeanCrossErrorConstant n β t*((q:ℝ)-r)/(N+1)*
    Real.sqrt (((q:ℝ)-r)/(N+1))) ?_ ?_)
  · apply Finset.sum_le_sum
    intro i _
    have hh := vectorMean_cross_cell_bound (n:=n) μ β t a hβ ht (T i.castSucc) (T i.succ) (hT (Fin.castSucc_le_succ i))
    simpa only [T,H,vectorUniformOverlapGrid_width,mul_div_assoc] using hh
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    field_simp
    exact le_rfl

theorem tendsto_vectorMeanLeftSum_cross_moment (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) :
    Tendsto (fun N =>∫sample : VectorDisorderBrownianSample n,
      inner ℝ (vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample)
        (vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample)∂vectorMeasureDisorderTilt μ β t a)
      atTop (𝓝 ((n:ℝ)*∫s in (r:ℝ)..(q:ℝ),vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc 0 1 zero_le_one s))) := by
  have hd : Tendsto (fun N : ℕ => ((q:ℝ)-r)/(N+1)) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul ((q:ℝ)-r)
    simpa only [mul_zero,div_eq_mul_inv,one_mul,Nat.cast_add,Nat.cast_one] using hh
  have he : Tendsto (fun N : ℕ =>vectorMeanCrossErrorConstant n β t*((q:ℝ)-r)*
      Real.sqrt (((q:ℝ)-r)/(N+1))) atTop (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).comp hd).const_mul (vectorMeanCrossErrorConstant n β t*((q:ℝ)-r))
  have hh := squeeze_zero_norm (fun N =>vectorMeanLeftSum_cross_sum_bound hn μ β t a hβ ht r q hrq N) he
  have hsum := tendsto_vectorMeanLeftSum_secondMoment hn μ β t a ht.le r q hrq
  simpa only [sub_add_cancel,zero_add] using hh.add hsum

end QuantitativePaper
