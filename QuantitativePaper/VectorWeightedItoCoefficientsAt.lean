module
public import QuantitativePaper.VectorShiftedGaussianMoments
public import QuantitativePaper.VectorWeightedItoCoefficients
public import QuantitativePaper.VectorItoCharacteristicsAt

@[expose] public section

/-! Genuine adapted Gaussian cancellation for the actual derivatives of a
test function, including a bounded initial-past multiplier. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
variable {a : ℝ≥0}
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
open FourPapersCommon
variable {n : ℕ}

theorem measurable_weightedVectorFirstAt
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (r : ℝ≥0) :
    Measurable[vectorBrownianFiltrationAt n a r] (weightedVectorFirst f X Z r) :=
  (hZ.mono ((vectorBrownianFiltrationAt n a).mono (bot_le : (0 : ℝ≥0) ≤ r)) le_rfl).smul
    (hf.adapted_first r)

theorem measurable_weightedVectorSecondAt
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (r : ℝ≥0) :
    Measurable[vectorBrownianFiltrationAt n a r] (weightedVectorSecond f X Z r) :=
  (hZ.mono ((vectorBrownianFiltrationAt n a).mono (bot_le : (0 : ℝ≥0) ≤ r)) le_rfl).smul
    (hf.adapted_second r)

theorem integrable_weightedVectorFirstAt
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r : ℝ≥0) :
    Integrable (weightedVectorFirst f X Z r) (vectorDisorderBrownianMeasure n) := by
  apply (integrable_const ((C : ℝ)*hf.firstBound)).mono'
    ((measurable_weightedVectorFirstAt hf Z hZ r).mono ((vectorBrownianFiltrationAt n a).le r)
      le_rfl).aestronglyMeasurable
  apply Eventually.of_forall
  intro sample
  rw [weightedVectorFirst,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC sample)
    (hf.first_le sample _) (norm_nonneg _) C.coe_nonneg

theorem integrable_weightedVectorSecondAt
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r : ℝ≥0) :
    Integrable (weightedVectorSecond f X Z r) (vectorDisorderBrownianMeasure n) := by
  apply (integrable_const ((C : ℝ)*hf.secondBound)).mono'
    ((measurable_weightedVectorSecondAt hf Z hZ r).mono ((vectorBrownianFiltrationAt n a).le r)
      le_rfl).aestronglyMeasurable
  apply Eventually.of_forall
  intro sample
  rw [weightedVectorSecond,norm_smul,Real.norm_eq_abs,vectorHessian_norm_eq]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC sample)
    (hf.second_le sample _) (norm_nonneg _) C.coe_nonneg

theorem integral_weighted_vector_gradient_noiseAt
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r t : ℝ≥0) (hrt : r ≤ t) (σ : ℝ) :
    (∫ sample,Z sample*fderiv ℝ (f sample) (X r sample)
      (σ • disorderVectorBrownianIncrementAt a r t sample) ∂vectorDisorderBrownianMeasure n)=0 := by
  have he : (fun sample=>Z sample*fderiv ℝ (f sample) (X r sample)
      (σ • disorderVectorBrownianIncrementAt a r t sample)) =
      (fun sample=>σ*(weightedVectorFirst f X Z r sample
        (disorderVectorBrownianIncrementAt a r t sample))) := by
    funext sample
    simp only [weightedVectorFirst,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul,integral_known_CLM_incrementAt a r t hrt _
    (measurable_weightedVectorFirstAt hf Z hZ r) (integrable_weightedVectorFirstAt hf Z hZ C hC r),mul_zero]

theorem integral_weighted_vector_hessian_noiseAt
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r t : ℝ≥0) (hrt : r ≤ t) (σ : ℝ) :
    (∫ sample,Z sample*vectorHessian (f sample) (X r sample)
      (σ • disorderVectorBrownianIncrementAt a r t sample)
      (σ • disorderVectorBrownianIncrementAt a r t sample) ∂vectorDisorderBrownianMeasure n) =
      σ^2*((t : ℝ)-r)*(∫ sample,Z sample*vectorBilinearTrace
        (vectorHessian (f sample) (X r sample)) ∂vectorDisorderBrownianMeasure n) := by
  have he : (fun sample=>Z sample*vectorHessian (f sample) (X r sample)
      (σ • disorderVectorBrownianIncrementAt a r t sample) (σ • disorderVectorBrownianIncrementAt a r t sample)) =
      (fun sample=>σ^2*(weightedVectorSecond f X Z r sample
        (disorderVectorBrownianIncrementAt a r t sample) (disorderVectorBrownianIncrementAt a r t sample))) := by
    funext sample
    simp only [weightedVectorSecond,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul,integral_known_bilinear_incrementAt a r t hrt _
    (measurable_weightedVectorSecondAt hf Z hZ r) (integrable_weightedVectorSecondAt hf Z hZ C hC r)]
  have ht (sample : VectorDisorderBrownianSample n) :
      vectorBilinearTrace (weightedVectorSecond f X Z r sample)=
        Z sample*vectorBilinearTrace (vectorHessian (f sample) (X r sample)) := by
    simp only [vectorBilinearTrace,weightedVectorSecond,ContinuousLinearMap.smul_apply,
      smul_eq_mul,Finset.mul_sum]
  simp only [ht]
  ring

end QuantitativePaper
