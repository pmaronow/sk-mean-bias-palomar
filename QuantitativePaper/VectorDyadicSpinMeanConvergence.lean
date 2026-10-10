module
public import QuantitativePaper.VectorNodeGradient
public import QuantitativePaper.VectorMeasureSpinLaw

@[expose] public section

/-! The actual finite-grid backward spin means converge to the genuine
arbitrary-profile spatial gradient along its constructed diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorMeasureSpinMean (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : Field n :=
  vectorMeasureGradient μ β t q sample.1
    (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample)

theorem tendsto_vectorDyadicSpinMean (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorDyadicSpinMean μ β t ht q j sample) atTop
      (𝓝 (vectorMeasureSpinMean μ β t ht q sample)) := by
  have hX := tendsto_vectorDyadicState_at_moving_time μ β t ht (q : ℝ).toNNReal
    (vectorDyadicTime q) (vectorDyadicTime_le_one q) (tendsto_vectorDyadicTime q) sample
  have hq := (Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex
  have hp : Tendsto (fun _ : ℕ=>sample.1) atTop (𝓝 sample.1) := tendsto_const_nhds
  have hz : Tendsto (fun j=>(Paper.parisiGridRound (vectorDyadicIndex j) q,
      (sample.1,vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample))) atTop
      (𝓝 (q,(sample.1,vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))) :=
    hq.prodMk_nhds (hp.prodMk_nhds hX)
  have hg : Tendsto (fun j=>vectorMeasureGradient μ β t
      (Paper.parisiGridRound (vectorDyadicIndex j) q) sample.1
      (vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample)) atTop
      (𝓝 (vectorMeasureSpinMean μ β t ht q sample)) := by
    change Tendsto
      ((fun z : Paper.Overlap×VectorParameter n=>vectorMeasureGradient μ β t z.1 z.2.1 z.2.2) ∘
        (fun j=>(Paper.parisiGridRound (vectorDyadicIndex j) q,
          (sample.1,vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample)))) atTop
      (𝓝 (vectorMeasureGradient μ β t q sample.1
        (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample)))
    exact ((continuous_vectorMeasureGradient μ β t ht).tendsto
      (q,(sample.1,vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))).comp hz
  have hd : Tendsto (fun j=>dist
      (vectorMeasureGradient μ β t (Paper.parisiGridRound (vectorDyadicIndex j) q) sample.1
        (vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample))
      (vectorDyadicSpinMean μ β t ht q j sample)) atTop (𝓝 0) := by
    exact squeeze_zero (fun _=>dist_nonneg)
      (fun j=>by
        rw [dist_comm]
        exact vectorDyadicTailGradient_limit_dist_le μ β t ht
          (Paper.parisiGridRound (vectorDyadicIndex j) q) j sample.1
          (vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample))
      (tendsto_vectorDyadicGradientError n β t)
  exact tendsto_of_tendsto_of_dist hg hd

theorem vectorDyadicSpinMean_component_bound (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) (l : Fin n) :
    |vectorDyadicSpinMean μ β t ht q j sample l|≤1 := by
  rw [vectorDyadicSpinMean_eq_backward,vectorBackwardMean_spin]
  exact vectorMagnetization_component_bound _ β t _ _ _ l

theorem vectorMeasureSpinMean_component_bound (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (l : Fin n) :
    |vectorMeasureSpinMean μ β t ht q sample l|≤1 := by
  have he := (EuclideanSpace.proj l).continuous.tendsto (vectorMeasureSpinMean μ β t ht q sample)
    |>.comp (tendsto_vectorDyadicSpinMean μ β t ht q sample)
  have he' : Tendsto (fun j=>vectorDyadicSpinMean μ β t ht q j sample l) atTop
      (𝓝 (vectorMeasureSpinMean μ β t ht q sample l)) := he
  apply le_of_tendsto he'.abs
  exact .of_forall fun j=>vectorDyadicSpinMean_component_bound μ β t ht q j sample l

end QuantitativePaper
