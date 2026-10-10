module
public import QuantitativePaper.VectorStochasticTaylor
public import QuantitativePaper.VectorGradientTimeLipschitz

@[expose] public section

/-! The true diffusion-gradient increment has the actual Hessian Brownian
term plus a uniform pathwise remainder. This follows from the constructed
time/spatial regularity and bounded drift, without a stochastic formula premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorGradientStochasticRemainderConstant (n : ℕ) (β t : ℝ) : ℝ :=
  Real.sqrt (n : ℝ)*vectorGradientTimeConstant n β t+
    (n : ℝ)*((1-t)*β^2)*Real.sqrt (n : ℝ)+vectorSpatialJetBound n 3*((1-t)*β^2)

theorem vectorGradientStochasticRemainderConstant_nonneg (β t : ℝ) (ht : t ≤ 1) :
    0 ≤ vectorGradientStochasticRemainderConstant n β t := by
  have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)
  unfold vectorGradientStochasticRemainderConstant
  exact add_nonneg (add_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (vectorGradientTimeConstant_nonneg n β t ht))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hc) (Real.sqrt_nonneg _)))
    (mul_nonneg (vectorSpatialJetBound_nonneg n 3) hc)

theorem vectorMeasureSpinMean_increment_remainder (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) (r q : Paper.Overlap) (hrq : r ≤ q)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample-
      Real.sqrt ((1-t)*β^2) • (vectorMeasureHessianProcess μ β t ht.le r sample
        (disorderVectorBrownianIncrement (r : ℝ).toNNReal (q : ℝ).toNNReal sample))‖ ≤
      vectorGradientStochasticRemainderConstant n β t*
        (((q : ℝ)-r)+‖disorderVectorBrownianIncrement (r : ℝ).toNNReal (q : ℝ).toNNReal sample‖^2) := by
  let Xq := vectorMeasureState μ β t ht.le (q : ℝ).toNNReal sample
  let Xr := vectorMeasureState μ β t ht.le (r : ℝ).toNNReal sample
  let B := disorderVectorBrownianIncrement (r : ℝ).toNNReal (q : ℝ).toNNReal sample
  let σ := Real.sqrt ((1-t)*β^2)
  let N := σ • B
  let c := (1-t)*β^2
  let A := Real.sqrt (n : ℝ)*vectorGradientTimeConstant n β t+(n : ℝ)*c*Real.sqrt (n : ℝ)
  let K := vectorSpatialJetBound n 3*c
  have hc : 0 ≤ c := mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg β)
  have hdt : 0 ≤ (q : ℝ)-r := sub_nonneg.mpr hrq
  have htime := vectorMeasureGradient_time_sub_le μ β t hβ ht sample.1 q r Xq
  rw [abs_of_nonneg hdt] at htime
  have hdrift := norm_vectorMeasureState_increment_sub_noise_le μ β t ht.le r q hrq sample
  have hspace := (vectorMeasureGradient_lipschitz μ β t ht.le r sample.1).norm_sub_le Xq (Xr+N)
  have hx : Xq-(Xr+N)=Xq-Xr-N := by abel
  rw [hx] at hspace
  have hspace' : ‖vectorMeasureGradient μ β t r sample.1 Xq-
      vectorMeasureGradient μ β t r sample.1 (Xr+N)‖ ≤
      ((n : ℝ)*c*Real.sqrt (n : ℝ))*((q : ℝ)-r) := by
    exact hspace.trans (by
      change (n : ℝ)*‖Xq-Xr-N‖ ≤ _
      have hh := mul_le_mul_of_nonneg_left hdrift (Nat.cast_nonneg n)
      simpa only [Xq, Xr, N, σ, B, c, mul_assoc] using hh)
  have htaylor := vectorMeasureGradient_firstTaylor_bound μ β t ht.le r sample.1 Xr N
  have hN : ‖N‖^2=c*‖B‖^2 := by
    dsimp only [N, σ]
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hc]
  rw [hN] at htaylor
  have he : vectorMeasureGradient μ β t q sample.1 Xq-
      vectorMeasureGradient μ β t r sample.1 Xr-vectorMeasureHessian μ β t r sample.1 Xr N =
      (vectorMeasureGradient μ β t q sample.1 Xq-vectorMeasureGradient μ β t r sample.1 Xq)+
      (vectorMeasureGradient μ β t r sample.1 Xq-vectorMeasureGradient μ β t r sample.1 (Xr+N))+
      (vectorMeasureGradient μ β t r sample.1 (Xr+N)-vectorMeasureGradient μ β t r sample.1 Xr-
        vectorMeasureHessian μ β t r sample.1 Xr N) := by abel
  have hraw : ‖vectorMeasureGradient μ β t q sample.1 Xq-
      vectorMeasureGradient μ β t r sample.1 Xr-vectorMeasureHessian μ β t r sample.1 Xr N‖ ≤
      A*((q : ℝ)-r)+K*‖B‖^2 := by
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add htime hspace')) htaylor)).trans_eq (by
        dsimp only [A, K]
        ring)
  have hA : 0 ≤ A := add_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (vectorGradientTimeConstant_nonneg n β t ht.le))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hc) (Real.sqrt_nonneg _))
  have hK : 0 ≤ K := mul_nonneg (vectorSpatialJetBound_nonneg n 3) hc
  have htotal : A*((q : ℝ)-r)+K*‖B‖^2 ≤ (A+K)*(((q : ℝ)-r)+‖B‖^2) := by
    nlinarith [mul_nonneg hA (sq_nonneg ‖B‖), mul_nonneg hK hdt]
  have h := hraw.trans htotal
  simpa only [vectorMeasureSpinMean, vectorMeasureHessianProcess, Xq, Xr, N,
    ContinuousLinearMap.map_smul, σ, B, A, K, c, vectorGradientStochasticRemainderConstant] using h

end QuantitativePaper
