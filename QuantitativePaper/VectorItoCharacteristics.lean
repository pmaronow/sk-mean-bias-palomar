module
public import QuantitativePaper.VectorWeightedDriftExpectation
public import FourPapersCommon.VectorGaussianMoments
public import FourPapersCommon.VectorDriftTaylor

@[expose] public section

/-! Analytic characteristics for a bounded drift driven by the actual vector
Wiener process. Future increment laws and cancellations are supplied by the
constructed Wiener measure, rather than assumed in these characteristics.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
open FourPapersCommon

structure VectorItoCharacteristics {n : ℕ}
    (X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (σ : ℝ) : Prop where
  continuous_state : ∀ sample,Continuous (fun q=>X q sample)
  measurable_state : Measurable (Function.uncurry X)
  adapted_state : StronglyAdapted (vectorBrownianFiltration n) X
  measurable_drift : Measurable (Function.uncurry d)
  bounded_drift : ∃ D : ℝ≥0,∀ q sample,‖d q sample‖ ≤ D
  decomposition : ∀ q sample,X q sample = X 0 sample+σ • disorderVectorBrownian q sample+
    vectorIntegratedDrift (fun s=>d s sample) q

structure VectorStaticItoTest {n : ℕ}
    (f : VectorDisorderBrownianSample n → Field n → ℝ)
    (X : ℝ≥0 → VectorDisorderBrownianSample n → Field n) where
  firstBound : ℝ≥0
  secondBound : ℝ≥0
  thirdBound : ℝ≥0
  measurable : Measurable (Function.uncurry f)
  regularity : ∀ sample,ContDiff ℝ 3 (f sample)
  first_le : ∀ sample x,‖fderiv ℝ (f sample) x‖ ≤ firstBound
  second_le : ∀ sample x,‖iteratedFDeriv ℝ 2 (f sample) x‖ ≤ secondBound
  third_le : ∀ sample x,‖iteratedFDeriv ℝ 3 (f sample) x‖ ≤ thirdBound
  adapted_first : ∀ q,Measurable[vectorBrownianFiltration n q]
    (fun sample=>fderiv ℝ (f sample) (X q sample))
  adapted_second : ∀ q,Measurable[vectorBrownianFiltration n q]
    (fun sample=>vectorHessian (f sample) (X q sample))

theorem VectorItoCharacteristics.increment {n : ℕ}
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ) (r t : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    X t sample = X r sample+σ • disorderVectorBrownianIncrement r t sample+
      (vectorIntegratedDrift (fun s=>d s sample) t-vectorIntegratedDrift (fun s=>d s sample) r) := by
  rw [hc.decomposition t sample,hc.decomposition r sample,disorderVectorBrownianIncrement,smul_sub]
  abel

theorem VectorStaticItoTest.continuous_first_path {n : ℕ}
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTest f X) (hX : ∀ sample,Continuous (fun q=>X q sample))
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun q=>fderiv ℝ (f sample) (X q sample)) := by
  exact ((hf.regularity sample).fderiv_right (m := 2) (by norm_num)).continuous.comp (hX sample)

theorem VectorStaticItoTest.continuous_second_path {n : ℕ}
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTest f X) (hX : ∀ sample,Continuous (fun q=>X q sample))
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun q=>vectorHessian (f sample) (X q sample)) := by
  exact (((hf.regularity sample).fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).continuous.comp (hX sample)

end QuantitativePaper
