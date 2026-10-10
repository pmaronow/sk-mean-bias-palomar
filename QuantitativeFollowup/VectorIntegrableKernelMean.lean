module
public import QuantitativeFollowup.VectorKernelScoreCentering
public import QuantitativePaper.VectorMeasureKernelScoreVariance

@[expose] public section

/-! Actual mean and offset integrability for nonnegative normalized kernels.
Bounds depend on their L1 mass and remain valid for unbounded L2 kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integrable_vectorMeasureKernelMean_of_integrable (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) (sample : VectorDisorderBrownianSample n) :
    Integrable (fun q=>κ q •vectorMeasureSpinMean μ β t ht q sample) (parisiFreeMeasure μ s) := by
  apply (hiκ.norm.mul_const (Real.sqrt (n:ℝ))).mono'
    (hκ.smul (continuous_vectorMeasureSpinMean_path μ β t ht sample).measurable).aestronglyMeasurable
  exact .of_forall fun q=>by
    change ‖κ q •vectorMeasureSpinMean μ β t ht q sample‖≤‖κ q‖*Real.sqrt (n:ℝ)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_vectorMeasureGradient_le μ β t ht q sample.1
      (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample)) (norm_nonneg (κ q))

theorem integrable_vectorMeasureKernelOffset_of_integrable (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) (sample : VectorDisorderBrownianSample n) :
    Integrable (fun q=>κ q*‖vectorMeasureSpinMean μ β t ht q sample‖^2/2) (parisiFreeMeasure μ s) := by
  apply (hiκ.norm.mul_const ((n:ℝ)/2)).mono'
    ((hκ.mul ((continuous_vectorMeasureSpinMean_path μ β t ht sample).measurable.norm.pow_const 2)).div_const 2).aestronglyMeasurable
  exact .of_forall fun q=>by
    change ‖κ q*‖vectorMeasureSpinMean μ β t ht q sample‖^2/2‖≤‖κ q‖*((n:ℝ)/2)
    rw [norm_div,norm_mul,Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    have h:=mul_le_mul_of_nonneg_left (norm_sq_le_dimension_of_components _
      (vectorMeasureSpinMean_component_bound μ β t ht q sample)) (norm_nonneg (κ q))
    exact (div_le_div_of_nonneg_right h (by norm_num)).trans_eq (by ring)

theorem vectorMeasureKernelMean_component_bound_normalized (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) (hκpos : ∀q,0≤κ q)
    (hnormal : (∫q,κ q ∂parisiFreeMeasure μ s)=1)
    (sample : VectorDisorderBrownianSample n) (i : Fin n) :
    ‖vectorMeasureKernelMean μ s β t ht κ sample i‖≤1 := by
  have he:=(EuclideanSpace.proj i).integral_comp_comm
    (integrable_vectorMeasureKernelMean_of_integrable μ s β t ht κ hκ hiκ sample)
  change (∫q,κ q*vectorMeasureSpinMean μ β t ht q sample i ∂parisiFreeMeasure μ s)=
    vectorMeasureKernelMean μ s β t ht κ sample i at he
  rw [←he]
  have h:=norm_integral_le_of_norm_le (f:=fun q=>κ q*vectorMeasureSpinMean μ β t ht q sample i) hiκ
    (.of_forall fun q=>by
      rw [norm_mul,Real.norm_of_nonneg (hκpos q)]
      have hb : ‖vectorMeasureSpinMean μ β t ht q sample i‖≤1:=by
        simpa only [Real.norm_eq_abs] using vectorMeasureSpinMean_component_bound μ β t ht q sample i
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (hκpos q))
  simpa only [hnormal] using h

theorem vectorMeasureKernelOffset_bound_normalized (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) (hκpos : ∀q,0≤κ q)
    (hnormal : (∫q,κ q ∂parisiFreeMeasure μ s)=1)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureKernelOffset μ s β t ht κ sample‖≤(n:ℝ)/2 := by
  have h:=norm_integral_le_of_norm_le (f:=fun q=>κ q*‖vectorMeasureSpinMean μ β t ht q sample‖^2/2)
    (hiκ.mul_const ((n:ℝ)/2)) (.of_forall fun q=>by
      rw [norm_div,norm_mul,Real.norm_of_nonneg (hκpos q),Real.norm_of_nonneg (sq_nonneg _),
        Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
      have h:=mul_le_mul_of_nonneg_left (norm_sq_le_dimension_of_components _
        (vectorMeasureSpinMean_component_bound μ β t ht q sample)) (hκpos q)
      exact (div_le_div_of_nonneg_right h (by norm_num)).trans_eq (by ring))
  simpa only [vectorMeasureKernelOffset,integral_mul_const,hnormal,one_mul] using h

theorem vectorMeasureWeightedOverlapScore_eq_affine_of_integrable (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (z : VectorDisorderBrownianSample n×Configuration n) :
    vectorMeasureWeightedOverlapScore μ s β t ht κ z=
      vectorMeasurePastAffineSpinScore (vectorMeasureKernelMean μ s β t ht κ)
        (vectorMeasureKernelOffset μ s β t ht κ) z := by
  have hi:=integrable_vectorMeasureKernelMean_of_integrable μ s β t ht κ hκ hiκ z.1
  have ho:=integrable_vectorMeasureKernelOffset_of_integrable μ s β t ht κ hκ hiκ z.1
  have hlin:=(fieldDotLinear z.2).integral_comp_comm hi
  simp only [fieldDotLinear_apply,map_smul,smul_eq_mul] at hlin
  have hli : Integrable (fun q=>κ q*fieldDot (vectorMeasureSpinMean μ β t ht q z.1) z.2)
      (parisiFreeMeasure μ s) := by
    simpa only [fieldDotLinear_apply,map_smul,smul_eq_mul] using (fieldDotLinear z.2).integrable_comp hi
  unfold vectorMeasureWeightedOverlapScore vectorMeasureOverlapScore normalizedSpinScore
  have halg (q : Paper.Overlap) : κ q*
      ((fieldDot (vectorMeasureSpinMean μ β t ht q z.1) z.2-‖vectorMeasureSpinMean μ β t ht q z.1‖^2/2)/(n:ℝ))=
      (κ q*fieldDot (vectorMeasureSpinMean μ β t ht q z.1) z.2-κ q*‖vectorMeasureSpinMean μ β t ht q z.1‖^2/2)/(n:ℝ) := by ring
  simp_rw [halg]
  rw [integral_div,integral_sub hli ho,hlin]
  rfl

end QuantitativeFollowup
