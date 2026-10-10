module
public import QuantitativePaper.VectorMeanStochasticMoments
public import QuantitativePaper.VectorSingleMatrixIsometry
public import QuantitativePaper.VectorStochasticGrid
public import QuantitativePaper.VectorGradientSquareIdentity
public import QuantitativeFollowup.VectorMeanIncrement

@[expose] public section

/-! Actual Brownian sums of the diffusion Hessian on any overlap interval.
Their exact second moments and genuine Riemann limit match the previously
proved spin-mean variance evolution. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorMeanLeftSum (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) : VectorDisorderBrownianSample n→Field n :=
  vectorMatrixBrownianSum (fun i => (vectorUniformOverlapGrid r q hrq N i:ℝ).toNNReal)
    (fun i => vectorMeanBrownianIntegrand μ β t ht (vectorUniformOverlapGrid r q hrq N i.castSucc))

theorem memLp_vectorMeanLeftSum (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) :
    MemLp (vectorMeanLeftSum (n:=n) μ β t ht r q hrq N) 2 (vectorMeasureDisorderTilt μ β t a) := by
  apply memLp_vectorMatrixBrownianSum μ β t a ht _
    (fun i j hij => Real.toNNReal_mono (monotone_vectorUniformOverlapGrid r q hrq N hij)) _
    (fun i => adapted_vectorMeanBrownianIntegrand μ β t ht _)
    (Real.sqrt ((1-t)*β^2)*(n:ℝ)).toNNReal
  intro i sample
  rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n))]
  exact norm_vectorMeanBrownianIntegrand_le μ β t ht _ sample

theorem integral_vectorMeanBrownianLocalTerm_norm_sq (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (r q : Paper.Overlap) (hrq : r≤q) :
    (∫sample : VectorDisorderBrownianSample n,‖vectorMeanBrownianIntegrand μ β t ht r sample
      (disorderVectorBrownianIncrement (r:ℝ).toNNReal (q:ℝ).toNNReal sample)‖^2∂vectorMeasureDisorderTilt μ β t a)=
      ((q:ℝ)-r)*((1-t)*β^2)*(∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht r sample∂vectorMeasureDisorderTilt μ β t a) := by
  rw [integral_tilted_bounded_matrix_increment_norm_sq μ β t a ht _ _ (Real.toNNReal_mono hrq) _
    (adapted_vectorMeanBrownianIntegrand μ β t ht r) (Real.sqrt ((1-t)*β^2)*(n:ℝ)).toNNReal
    (fun sample => by
      rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n))]
      exact norm_vectorMeanBrownianIntegrand_le μ β t ht r sample)]
  simp_rw [vectorMeanBrownianIntegrand_hilbertSquare]
  rw [integral_const_mul,Real.coe_toNNReal _ q.property.1,Real.coe_toNNReal _ r.property.1]
  ring

theorem vectorMeanLeftSum_secondMoment (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) :
    (∫sample,‖vectorMeanLeftSum (n:=n) μ β t ht r q hrq N sample‖^2∂vectorMeasureDisorderTilt μ β t a)=
      ∑i : Fin (N+1),(n:ℝ)*vectorMeanOverlapDerivative (n:=n) μ β t a ht
        (vectorUniformOverlapGrid r q hrq N i.castSucc)*
        ((vectorUniformOverlapGrid r q hrq N i.succ:ℝ)-vectorUniformOverlapGrid r q hrq N i.castSucc) := by
  rw [vectorMeanLeftSum,integral_vectorMatrixBrownianSum_norm_sq μ β t a ht _
    (fun i j hij => Real.toNNReal_mono (monotone_vectorUniformOverlapGrid r q hrq N hij)) _
    (fun i => adapted_vectorMeanBrownianIntegrand μ β t ht _)
    (Real.sqrt ((1-t)*β^2)*(n:ℝ)).toNNReal (fun i sample => by
      rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n))]
      exact norm_vectorMeanBrownianIntegrand_le μ β t ht _ sample)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [vectorMeanBrownianIntegrand_hilbertSquare]
  rw [integral_const_mul,Real.coe_toNNReal _ (vectorUniformOverlapGrid r q hrq N i.succ).property.1,
    Real.coe_toNNReal _ (vectorUniformOverlapGrid r q hrq N i.castSucc).property.1]
  unfold vectorMeanOverlapDerivative
  field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0:ℝ)<n)]

theorem tendsto_vectorMeanLeftSum_secondMoment (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (r q : Paper.Overlap) (hrq : r≤q) :
    Tendsto (fun N =>∫sample,‖vectorMeanLeftSum (n:=n) μ β t ht r q hrq N sample‖^2∂vectorMeasureDisorderTilt μ β t a)
      atTop (𝓝 ((n:ℝ)*∫s in (r:ℝ)..(q:ℝ),vectorMeanOverlapDerivative (n:=n) μ β t a ht (projIcc 0 1 zero_le_one s))) := by
  simp_rw [vectorMeanLeftSum_secondMoment hn μ β t a ht r q hrq]
  have hf : Continuous (fun s : ℝ => (n:ℝ)*vectorMeanOverlapDerivative (n:=n) μ β t a ht (projIcc 0 1 zero_le_one s)) :=
    ((continuous_vectorMeanOverlapDerivative (n:=n) μ β t a ht).comp continuous_projIcc).const_mul _
  have h := vectorUniformOverlapGrid_riemann_tendsto r q hrq _ hf
  simpa only [projIcc_val,intervalIntegral.integral_const_mul] using h

theorem vectorMean_increment_variance_integral (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) :
    (∫sample,‖vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample‖^2
      ∂vectorMeasureDisorderTilt (n:=n) μ β t a)=
      (n:ℝ)*∫s in (r:ℝ)..(q:ℝ),vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc 0 1 zero_le_one s) := by
  rw [QuantitativeFollowup.vector_spinMean_increment_second_moment hn μ β t a hβ ht r q hrq]
  have h := vectorMeanOverlapReal_interval_integral (n:=n) μ β t a hβ ht r.property q.property
  simpa only [QuantitativeFollowup.vectorMeanOverlapReal,
    projIcc_of_mem zero_le_one q.property,projIcc_of_mem zero_le_one r.property] using congrArg ((n:ℝ)*·) h

end QuantitativePaper
