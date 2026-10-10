module
public import QuantitativePaper.VectorMildSource
public import QuantitativePaper.VectorMeasureEndpoints

@[expose] public section

/-! Actual convergence of the nonlinear Duhamel correction, retaining the
merely measurable Parisi CDF coefficient. No mild equation is an input to
these approximation statements. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000

def vectorMeasureMildCorrection {n : ℕ} (μ : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  ((1-t)*β^2)/2*∫ s in (q : ℝ)..1,
    vectorMildSource μ (vectorMeasureGradient μ β t) ((1-t)*β^2) q s p x

def vectorDyadicMildCorrection {n : ℕ} (μ : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (j : ℕ) (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  ((1-t)*β^2)/2*∫ s in (q : ℝ)..1,
    vectorMildSource (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (fun r p y => vectorDyadicTailGradient μ β t r j p y) ((1-t)*β^2) q s p x

def vectorDyadicGradientError (n : ℕ) (β t : ℝ) (j : ℕ) : ℝ :=
  ((4*(n : ℝ)*((1-t)*β^2)+2*n)/(1-vectorGradientDecay))*vectorGradientDecay^j

theorem vectorDyadicGradientError_nonneg (n : ℕ) (β t : ℝ) (ht : t≤1) (j : ℕ) :
    0≤vectorDyadicGradientError n β t j := by
  have hr := vectorGradientDecay_lt_one
  have hp := vectorGradientDecay_pos
  unfold vectorDyadicGradientError
  positivity

theorem tendsto_vectorDyadicGradientError (n : ℕ) (β t : ℝ) :
    Tendsto (vectorDyadicGradientError n β t) atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => ((4*(n : ℝ)*((1-t)*β^2)+2*n)/
    (1-vectorGradientDecay))*vectorGradientDecay^j) atTop (𝓝 0)
  simpa only [vectorDyadicGradientError,mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one vectorGradientDecay_pos.le
      vectorGradientDecay_lt_one).const_mul
      ((4*(n : ℝ)*((1-t)*β^2)+2*n)/(1-vectorGradientDecay))

theorem vectorDyadicMildCorrection_abs_sub_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (j : ℕ)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorMeasureMildCorrection μ β t q p x-vectorDyadicMildCorrection μ β t q j p x|≤
      ((1-t)*β^2)/2*((n : ℝ)*Paper.parisiCDFDistance μ
        (Paper.parisiGridMeasure μ (vectorDyadicIndex j))+
        2*Real.sqrt (n : ℝ)*vectorDyadicGradientError n β t j) := by
  unfold vectorMeasureMildCorrection vectorDyadicMildCorrection
  rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤((1-t)*β^2)/2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply vectorMildSource_integral_sub_le μ (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
    (vectorMeasureGradient μ β t) (fun r p y => vectorDyadicTailGradient μ β t r j p y)
    (measurable_vectorMeasureGradient μ β t ht) (measurable_vectorFiniteTailGradient _ β t)
    (fun r p y => norm_vectorMeasureGradient_le μ β t ht r p y)
    (fun r p y => norm_vectorFiniteTailGradient_le _ β t r p y)
    (vectorDyadicGradientError n β t j) (vectorDyadicGradientError_nonneg n β t ht j)
  intro r p y
  rw [dist_comm]
  exact vectorDyadicTailGradient_limit_dist_le μ β t ht r j p y

theorem tendstoUniformly_vectorDyadicMildCorrection {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    TendstoUniformly (fun j => fun z : Paper.Overlap×VectorParameter n =>
      vectorDyadicMildCorrection μ β t z.1 j z.2.1 z.2.2)
      (fun z => vectorMeasureMildCorrection μ β t z.1 z.2.1 z.2.2) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hD := (Paper.tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex
  have hE := tendsto_vectorDyadicGradientError n β t
  have hh : Tendsto (fun j => ((1-t)*β^2)/2*((n : ℝ)*Paper.parisiCDFDistance μ
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j))+
      2*Real.sqrt (n : ℝ)*vectorDyadicGradientError n β t j)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add,Function.comp_def] using
      ((hD.const_mul (n : ℝ)).add (hE.const_mul (2*Real.sqrt (n : ℝ)))).const_mul (((1-t)*β^2)/2)
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with j hj
  intro z
  rw [Real.dist_eq]
  exact (vectorDyadicMildCorrection_abs_sub_le μ β t ht z.1 j z.2.1 z.2.2).trans_lt hj

end QuantitativePaper
