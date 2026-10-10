module
public import QuantitativePaper.VectorFiniteMeasureStateStability
public import QuantitativePaper.VectorMildLimit

@[expose] public section

/-! The actual finite-grid diffusions converge, on the same Wiener space,
to the actual arbitrary-profile diffusion. This compares their genuine
finite gradients directly with the selected uniform gradient limit. -/
noncomputable section
open Set MeasureTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorDyadicState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1) (j : ℕ)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : Field n :=
  vectorFiniteState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht r sample

def vectorDyadicStateError (n : ℕ) (μ : Paper.ParisiMeasure) (β t : ℝ) (j : ℕ) : ℝ :=
  (((1-t)*β^2)*Real.exp (((1-t)*β^2)*(n : ℝ)))*
    (Real.sqrt n*Paper.parisiCDFDistance μ (Paper.parisiGridMeasure μ (vectorDyadicIndex j))+
      vectorDyadicGradientError n β t j)

theorem norm_vectorMeasureState_sub_dyadic_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (j : ℕ) (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureState μ β t ht r sample-vectorDyadicState μ β t ht j r sample‖≤
      vectorDyadicStateError n μ β t j := by
  have he := norm_vectorMeasureState_sub_finite_le μ
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
    (vectorDyadicGradientError n β t j) (vectorDyadicGradientError_nonneg n β t ht j)
    (fun q p x=>by
      rw [←dist_eq_norm,dist_comm]
      exact vectorDyadicTailGradient_limit_dist_le μ β t ht q j p x) r hr sample
  simpa only [vectorDyadicState,vectorDyadicStateError,FRSB.parisiSchemeMeasure_grid_eq] using he

theorem tendsto_vectorDyadicStateError (n : ℕ) (μ : Paper.ParisiMeasure) (β t : ℝ) :
    Tendsto (vectorDyadicStateError n μ β t) atTop (𝓝 0) := by
  change Tendsto (fun j=>(((1-t)*β^2)*Real.exp (((1-t)*β^2)*(n : ℝ)))*
    (Real.sqrt n*Paper.parisiCDFDistance μ (Paper.parisiGridMeasure μ (vectorDyadicIndex j))+
      vectorDyadicGradientError n β t j)) atTop (𝓝 0)
  have hD := (Paper.tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex
  have hE := tendsto_vectorDyadicGradientError n β t
  simpa only [vectorDyadicStateError,Function.comp_def,mul_zero,add_zero] using
    ((hD.const_mul (Real.sqrt n)).add hE).const_mul
      (((1-t)*β^2)*Real.exp (((1-t)*β^2)*(n : ℝ)))

theorem tendstoUniformlyOn_vectorDyadicState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1) :
    TendstoUniformlyOn
      (fun j=>fun z : ℝ≥0×VectorDisorderBrownianSample n=>vectorDyadicState μ β t ht j z.1 z.2)
      (fun z=>vectorMeasureState μ β t ht z.1 z.2) atTop
      (Icc (0 : ℝ≥0) 1 ×ˢ univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_vectorDyadicStateError n μ β t).eventually (gt_mem_nhds hε)] with j hj
  intro z hz
  rw [dist_eq_norm]
  exact (norm_vectorMeasureState_sub_dyadic_le μ β t ht j z.1 hz.1.2 z.2).trans_lt hj

theorem tendsto_vectorDyadicState_at_moving_time (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (r : ℝ≥0) (R : ℕ→ℝ≥0) (hR : ∀ j,R j≤1)
    (hRt : Tendsto R atTop (𝓝 r)) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorDyadicState μ β t ht j (R j) sample) atTop
      (𝓝 (vectorMeasureState μ β t ht r sample)) := by
  have hX : Tendsto (fun j=>vectorMeasureState μ β t ht (R j) sample) atTop
      (𝓝 (vectorMeasureState μ β t ht r sample)) := by
    simpa only [Function.comp_def] using
      (continuous_vectorMeasureState μ β t ht sample).tendsto r |>.comp hRt
  have hd : Tendsto (fun j=>dist (vectorDyadicState μ β t ht j (R j) sample)
      (vectorMeasureState μ β t ht (R j) sample)) atTop (𝓝 0) := by
    exact squeeze_zero (fun _=>dist_nonneg)
      (fun j=>by
        rw [dist_comm,dist_eq_norm]
        exact norm_vectorMeasureState_sub_dyadic_le μ β t ht j _ (hR j) sample)
      (tendsto_vectorDyadicStateError n μ β t)
  exact tendsto_of_tendsto_of_dist hX (by simpa only [dist_comm] using hd)

end QuantitativePaper
