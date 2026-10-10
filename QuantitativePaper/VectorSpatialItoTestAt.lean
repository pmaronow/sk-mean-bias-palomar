module
public import QuantitativePaper.VectorShiftedGaussianMoments
public import QuantitativePaper.VectorItoStepAt
public import FourPapersCommon.BoundedRiemannExpectation

@[expose] public section

/-! Uniform spatial tests with deterministic time dependence. Each actual
spatial slice has adapted derivatives, and diagonal gradient and trace paths
are continuous. These are analytic regularity requirements, not stochastic
identity assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
variable {a : ℝ≥0}
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

structure VectorSpatialItoTestAt (a : ℝ≥0)
    (f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ)
    (X : ℝ≥0 → VectorDisorderBrownianSample n → Field n) where
  firstBound : ℝ≥0
  secondBound : ℝ≥0
  thirdBound : ℝ≥0
  measurable : ∀ q,Measurable (Function.uncurry (f q))
  regularity : ∀ q sample,ContDiff ℝ 3 (f q sample)
  first_le : ∀ q sample x,‖fderiv ℝ (f q sample) x‖ ≤ firstBound
  second_le : ∀ q sample x,‖iteratedFDeriv ℝ 2 (f q sample) x‖ ≤ secondBound
  third_le : ∀ q sample x,‖iteratedFDeriv ℝ 3 (f q sample) x‖ ≤ thirdBound
  adapted_first : ∀ q r,Measurable[vectorBrownianFiltrationAt n a r]
    (fun sample=>fderiv ℝ (f q sample) (X r sample))
  adapted_second : ∀ q r,Measurable[vectorBrownianFiltrationAt n a r]
    (fun sample=>vectorHessian (f q sample) (X r sample))
  continuous_first_path : ∀ sample,Continuous (fun q=>fderiv ℝ (f q sample) (X q sample))
  continuous_trace_path : ∀ sample,Continuous (fun q=>vectorBilinearTrace (vectorHessian (f q sample) (X q sample)))

def VectorSpatialItoTestAt.slice
    {f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorSpatialItoTestAt a f X) (q : ℝ≥0) : VectorStaticItoTestAt a (f q) X where
  firstBound := hf.firstBound
  secondBound := hf.secondBound
  thirdBound := hf.thirdBound
  measurable := hf.measurable q
  regularity := hf.regularity q
  first_le := hf.first_le q
  second_le := hf.second_le q
  third_le := hf.third_le q
  adapted_first := hf.adapted_first q
  adapted_second := hf.adapted_second q

theorem VectorSpatialItoTestAt.trace_bound
    {f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorSpatialItoTestAt a f X) (q : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    |vectorBilinearTrace (vectorHessian (f q sample) (X q sample))| ≤ n*hf.secondBound := by
  have hH : ‖vectorHessian (f q sample) (X q sample)‖ ≤ hf.secondBound := by
    rw [vectorHessian_norm_eq]
    exact hf.second_le q sample _
  calc
    _ ≤ ∑ i : Fin n,|vectorHessian (f q sample) (X q sample)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n,(hf.secondBound : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [PiLp.norm_single,norm_one,mul_one] using vectorHessian_apply_bound hH
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end QuantitativePaper
