module
public import QuantitativePaper.VectorItoCharacteristics

@[expose] public section

/-! Genuine adapted Gaussian cancellation for the actual derivatives of a
test function, including a bounded initial-past multiplier. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
open FourPapersCommon
variable {n : ℕ}

def weightedVectorFirst (f : VectorDisorderBrownianSample n → Field n → ℝ)
    (X : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (Z : VectorDisorderBrownianSample n → ℝ) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : Field n →L[ℝ] ℝ :=
  Z sample • fderiv ℝ (f sample) (X r sample)

def weightedVectorSecond (f : VectorDisorderBrownianSample n → Field n → ℝ)
    (X : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (Z : VectorDisorderBrownianSample n → ℝ) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : Field n →L[ℝ] Field n →L[ℝ] ℝ :=
  Z sample • vectorHessian (f sample) (X r sample)

theorem measurable_weightedVectorFirst
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTest f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (r : ℝ≥0) :
    Measurable[vectorBrownianFiltration n r] (weightedVectorFirst f X Z r) :=
  (hZ.mono ((vectorBrownianFiltration n).mono (bot_le : (0 : ℝ≥0) ≤ r)) le_rfl).smul
    (hf.adapted_first r)

theorem measurable_weightedVectorSecond
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTest f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (r : ℝ≥0) :
    Measurable[vectorBrownianFiltration n r] (weightedVectorSecond f X Z r) :=
  (hZ.mono ((vectorBrownianFiltration n).mono (bot_le : (0 : ℝ≥0) ≤ r)) le_rfl).smul
    (hf.adapted_second r)

theorem integrable_weightedVectorFirst
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTest f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r : ℝ≥0) :
    Integrable (weightedVectorFirst f X Z r) (vectorDisorderBrownianMeasure n) := by
  apply (integrable_const ((C : ℝ)*hf.firstBound)).mono'
    ((measurable_weightedVectorFirst hf Z hZ r).mono ((vectorBrownianFiltration n).le r)
      le_rfl).aestronglyMeasurable
  apply Eventually.of_forall
  intro sample
  rw [weightedVectorFirst,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC sample)
    (hf.first_le sample _) (norm_nonneg _) C.coe_nonneg

theorem integrable_weightedVectorSecond
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTest f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r : ℝ≥0) :
    Integrable (weightedVectorSecond f X Z r) (vectorDisorderBrownianMeasure n) := by
  apply (integrable_const ((C : ℝ)*hf.secondBound)).mono'
    ((measurable_weightedVectorSecond hf Z hZ r).mono ((vectorBrownianFiltration n).le r)
      le_rfl).aestronglyMeasurable
  apply Eventually.of_forall
  intro sample
  rw [weightedVectorSecond,norm_smul,Real.norm_eq_abs,vectorHessian_norm_eq]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC sample)
    (hf.second_le sample _) (norm_nonneg _) C.coe_nonneg

theorem integral_weighted_vector_gradient_noise
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTest f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r t : ℝ≥0) (hrt : r ≤ t) (σ : ℝ) :
    (∫ sample,Z sample*fderiv ℝ (f sample) (X r sample)
      (σ • disorderVectorBrownianIncrement r t sample) ∂vectorDisorderBrownianMeasure n)=0 := by
  have he : (fun sample=>Z sample*fderiv ℝ (f sample) (X r sample)
      (σ • disorderVectorBrownianIncrement r t sample)) =
      (fun sample=>σ*(weightedVectorFirst f X Z r sample
        (disorderVectorBrownianIncrement r t sample))) := by
    funext sample
    simp only [weightedVectorFirst,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul,integral_known_CLM_increment r t hrt _
    (measurable_weightedVectorFirst hf Z hZ r) (integrable_weightedVectorFirst hf Z hZ C hC r),mul_zero]

theorem integral_weighted_vector_hessian_noise
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTest f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r t : ℝ≥0) (hrt : r ≤ t) (σ : ℝ) :
    (∫ sample,Z sample*vectorHessian (f sample) (X r sample)
      (σ • disorderVectorBrownianIncrement r t sample)
      (σ • disorderVectorBrownianIncrement r t sample) ∂vectorDisorderBrownianMeasure n) =
      σ^2*((t : ℝ)-r)*(∫ sample,Z sample*vectorBilinearTrace
        (vectorHessian (f sample) (X r sample)) ∂vectorDisorderBrownianMeasure n) := by
  have he : (fun sample=>Z sample*vectorHessian (f sample) (X r sample)
      (σ • disorderVectorBrownianIncrement r t sample) (σ • disorderVectorBrownianIncrement r t sample)) =
      (fun sample=>σ^2*(weightedVectorSecond f X Z r sample
        (disorderVectorBrownianIncrement r t sample) (disorderVectorBrownianIncrement r t sample))) := by
    funext sample
    simp only [weightedVectorSecond,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul,integral_known_bilinear_increment r t hrt _
    (measurable_weightedVectorSecond hf Z hZ r) (integrable_weightedVectorSecond hf Z hZ C hC r)]
  have ht (sample : VectorDisorderBrownianSample n) :
      vectorBilinearTrace (weightedVectorSecond f X Z r sample)=
        Z sample*vectorBilinearTrace (vectorHessian (f sample) (X r sample)) := by
    simp only [vectorBilinearTrace,weightedVectorSecond,ContinuousLinearMap.smul_apply,
      smul_eq_mul,Finset.mul_sum]
  simp only [ht]
  ring

end QuantitativePaper
