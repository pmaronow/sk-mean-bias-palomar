module
public import QuantitativePaper.VectorMeasureHessianProcess
public import FourPapersCommon.DerivativeInterpolation

@[expose] public section

/-! Genuine spatial Taylor control and the exact bounded-drift correction
to the Wiener increment. These are pathwise estimates used by the stochastic
Riemann-sum proof. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem vectorMeasureGradient_firstTaylor_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x v : Field n) :
    ‖vectorMeasureGradient μ β t q p (x+v)-vectorMeasureGradient μ β t q p x-
      vectorMeasureHessian μ β t q p x v‖ ≤ vectorSpatialJetBound n 3*‖v‖^2 := by
  have hG := contDiff_vectorMeasureGradient μ β t ht q p
  have hK := vectorSpatialJetBound_nonneg n 3
  have hb (y : Field n) : ‖iteratedFDeriv ℝ 2 (vectorMeasureGradient μ β t q p) y‖ ≤
      vectorSpatialJetBound n 3 := by
    rw [funext (vectorMeasureGradient_eq_gradient μ β t ht q p),
      QuantitativeFollowup.norm_iteratedFDeriv_gradient]
    exact norm_vectorMeasureTailPotential_jet_le_uniform μ β t ht q p 3 (by omega) y
  have hLip := lipschitz_fderiv_of_secondJet_bound _ hG _ hK hb
  have hT := firstTaylor_remainder_Banach (E := Field n) (F := Field n)
    (vectorMeasureGradient μ β t q p) (hG.differentiable (by simp))
    (vectorSpatialJetBound n 3).toNNReal hLip x v
  rw [(hasFDerivAt_vectorMeasureGradient μ β t ht q p x).fderiv,
    Real.coe_toNNReal _ hK] at hT
  exact hT

theorem norm_vectorAdditiveState_increment_sub_noise_le (d : VectorAdditiveDriftData n)
    (σ : ℝ) (x0 : Field n) (T r u : ℝ≥0) (hru : r ≤ u)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorAdditiveState d σ x0 T u sample-vectorAdditiveState d σ x0 T r sample-
      σ • disorderVectorBrownianIncrement r u sample‖ ≤ d.bound*((u : ℝ)-r) := by
  have he : vectorAdditiveState d σ x0 T u sample-vectorAdditiveState d σ x0 T r sample-
      σ • disorderVectorBrownianIncrement r u sample =
      vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s sample) u-
        vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s sample) r := by
    rw [vectorAdditiveState_decomposition, vectorAdditiveState_decomposition]
    simp only [disorderVectorBrownianIncrement, smul_sub]
    abel
  rw [he]
  exact vectorIntegratedDrift_increment_bound _
    (measurable_uncurry_vectorAdditiveDrift d σ x0 T).of_uncurry_right d.bound
    (fun s => norm_vectorAdditiveDrift_le d σ x0 T s sample) hru

theorem norm_vectorMeasureState_increment_sub_noise_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (r q : Paper.Overlap) (hrq : r ≤ q)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureState μ β t ht (q : ℝ).toNNReal sample-
      vectorMeasureState μ β t ht (r : ℝ).toNNReal sample-
      Real.sqrt ((1-t)*β^2) • disorderVectorBrownianIncrement (r : ℝ).toNNReal (q : ℝ).toNNReal sample‖
      ≤ ((1-t)*β^2)*Real.sqrt (n : ℝ)*((q : ℝ)-r) := by
  have h := norm_vectorAdditiveState_increment_sub_noise_le (vectorMeasureDriftData (n := n) μ β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1 (r : ℝ).toNNReal (q : ℝ).toNNReal
    (Real.toNNReal_mono hrq) sample
  change ‖vectorMeasureState μ β t ht (q : ℝ).toNNReal sample-
    vectorMeasureState μ β t ht (r : ℝ).toNNReal sample-
    Real.sqrt ((1-t)*β^2) • disorderVectorBrownianIncrement (r : ℝ).toNNReal (q : ℝ).toNNReal sample‖ ≤
    ((1-t)*β^2)*Real.sqrt (n : ℝ)*
      (((q : ℝ).toNNReal : ℝ)-((r : ℝ).toNNReal : ℝ)) at h
  simpa only [Real.coe_toNNReal _ r.property.1, Real.coe_toNNReal _ q.property.1] using h

end QuantitativePaper
