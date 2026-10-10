module
public import QuantitativePaper.GradientStability
public import QuantitativePaper.VectorMeasureTail

@[expose] public section

/-! The genuine uniform gradient limit of the actual dyadic vector
potentials. The convergence is derived from value stability and the actual
dimension-only Hessian bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 500000

def vectorGradientDecay : ℝ := Real.sqrt (1/2 : ℝ)

theorem vectorGradientDecay_pos : 0<vectorGradientDecay := by
  exact Real.sqrt_pos.mpr (by norm_num)

theorem vectorGradientDecay_lt_one : vectorGradientDecay<1 := by
  unfold vectorGradientDecay
  exact (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)

theorem vectorGradientDecay_sq : vectorGradientDecay^2=(1/2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

def vectorDyadicTailGradient {n : ℕ} (μ : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (j : ℕ) (p : Couplings n×ℝ) (x : Field n) : Field n :=
  vectorFiniteTailGradient (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q p x

theorem vectorDyadicTailGradient_eq_gradient {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (q : Paper.Overlap) (j : ℕ) (p : Couplings n×ℝ) (x : Field n) :
    vectorDyadicTailGradient μ β t q j p x=
      gradient (vectorDyadicTailPotential μ β t q j p) x := rfl

theorem differentiable_vectorDyadicTailPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (q : Paper.Overlap) (j : ℕ) (p : Couplings n×ℝ) :
    Differentiable ℝ (vectorDyadicTailPotential μ β t q j p) := by
  unfold vectorDyadicTailPotential
  rw [vectorTailRecursion_eq_clamped _ β t q q.property p le_rfl]
  exact (contDiff_vectorRecursion_field _ β t p _).differentiable (by simp)

theorem vectorDyadicTailGradient_succ_dist_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (j : ℕ)
    (p : Couplings n×ℝ) (x : Field n) :
    dist (vectorDyadicTailGradient μ β t q (j+1) p x)
      (vectorDyadicTailGradient μ β t q j p x) ≤
      (4*(n : ℝ)*((1-t)*β^2)+2*n)*vectorGradientDecay^j := by
  let ε := (2*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j
  let δ := vectorGradientDecay^j
  have hδ : 0<δ := pow_pos vectorGradientDecay_pos j
  have hδsq : δ^2=(1/2 : ℝ)^j := by
    dsimp only [δ]
    rw [←pow_mul,mul_comm j 2,pow_mul,vectorGradientDecay_sq]
  have hh := norm_gradient_sub_le_of_uniform_sub
    (vectorDyadicTailPotential μ β t q (j+1) p) (vectorDyadicTailPotential μ β t q j p)
    (differentiable_vectorDyadicTailPotential μ β t q (j+1) p)
    (differentiable_vectorDyadicTailPotential μ β t q j p) (n : ℝ≥0)
    (vectorFiniteTailGradient_lipschitz _ β t q p)
    (vectorFiniteTailGradient_lipschitz _ β t q p)
    ε (by dsimp only [ε];positivity)
    (fun y => vectorDyadicTailPotential_succ_abs_sub_le μ β t q ht q.property j p y)
    δ hδ x
  rw [dist_eq_norm,vectorDyadicTailGradient_eq_gradient,vectorDyadicTailGradient_eq_gradient]
  refine hh.trans_eq ?_
  dsimp only [ε]
  rw [←hδsq,NNReal.coe_natCast]
  change 2*(2*(n : ℝ)*((1-t)*β^2)*δ^2)/δ+2*(n : ℝ)*δ=
    (4*(n : ℝ)*((1-t)*β^2)+2*n)*δ
  field_simp
  ring

theorem cauchySeq_vectorDyadicTailGradient {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    CauchySeq (fun j => vectorDyadicTailGradient μ β t q j p x) := by
  apply cauchySeq_of_le_geometric vectorGradientDecay
    (4*(n : ℝ)*((1-t)*β^2)+2*n) vectorGradientDecay_lt_one
  intro j
  rw [dist_comm]
  exact vectorDyadicTailGradient_succ_dist_le μ β t ht q j p x

def vectorMeasureGradient {n : ℕ} (μ : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) : Field n :=
  limUnder atTop (fun j => vectorDyadicTailGradient μ β t q j p x)

theorem tendsto_vectorDyadicTailGradient {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    Tendsto (fun j => vectorDyadicTailGradient μ β t q j p x) atTop
      (𝓝 (vectorMeasureGradient μ β t q p x)) :=
  (cauchySeq_vectorDyadicTailGradient μ β t ht q p x).tendsto_limUnder

theorem vectorDyadicTailGradient_limit_dist_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (j : ℕ)
    (p : Couplings n×ℝ) (x : Field n) :
    dist (vectorDyadicTailGradient μ β t q j p x) (vectorMeasureGradient μ β t q p x) ≤
      ((4*(n : ℝ)*((1-t)*β^2)+2*n)/(1-vectorGradientDecay))*vectorGradientDecay^j := by
  have hh := dist_le_of_le_geometric_of_tendsto (r:=vectorGradientDecay)
    (C:=4*(n : ℝ)*((1-t)*β^2)+2*n) vectorGradientDecay_lt_one
    (fun l => by rw [dist_comm];exact vectorDyadicTailGradient_succ_dist_le μ β t ht q l p x)
    (tendsto_vectorDyadicTailGradient μ β t ht q p x) j
  convert hh using 1
  ring

theorem tendstoUniformly_vectorDyadicTailGradient {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    TendstoUniformly (fun j => fun z : Paper.Overlap×VectorParameter n =>
      vectorDyadicTailGradient μ β t z.1 j z.2.1 z.2.2)
      (fun z => vectorMeasureGradient μ β t z.1 z.2.1 z.2.2) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hh : Tendsto (fun j : ℕ => ((4*(n : ℝ)*((1-t)*β^2)+2*n)/
      (1-vectorGradientDecay))*vectorGradientDecay^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one vectorGradientDecay_pos.le
        vectorGradientDecay_lt_one).const_mul
        ((4*(n : ℝ)*((1-t)*β^2)+2*n)/(1-vectorGradientDecay))
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with j hj
  intro z
  rw [dist_comm]
  exact (vectorDyadicTailGradient_limit_dist_le μ β t ht z.1 j z.2.1 z.2.2).trans_lt hj

end QuantitativePaper
