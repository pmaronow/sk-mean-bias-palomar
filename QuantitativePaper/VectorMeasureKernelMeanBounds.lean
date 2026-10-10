module
public import QuantitativePaper.VectorMeasureKernelMean

@[expose] public section

/-! Integrability and actual uniform bounds for deterministic-kernel spin
means and offsets under the actual free Parisi measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000

theorem parisiFree_norm_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (f : Paper.Overlap→E) (B : ℝ) (hB : 0≤B) (hb : ∀q,‖f q‖≤B) :
    ‖∫q,f q ∂parisiFreeMeasure μ s‖≤B := by
  have hi:=norm_integral_le_of_norm_le (f:=f)
    (integrable_const B : Integrable _ (parisiFreeMeasure μ s)) (.of_forall hb)
  have he : (∫_q : Paper.Overlap,B ∂parisiFreeMeasure μ s)=(1-s)*B := by
    simp only [integral_const,Measure.real,parisiFreeMeasure_univ,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2),smul_eq_mul]
  rw [he] at hi
  exact hi.trans (by nlinarith [mul_nonneg hs.1 hB])

theorem integrable_vectorMeasureKernelMean (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K)
    (hB : ∀q,|κ q|≤K) (sample : VectorDisorderBrownianSample n) :
    Integrable (fun q=>κ q •vectorMeasureSpinMean μ β t ht q sample) (parisiFreeMeasure μ s) := by
  apply (integrable_const (K*Real.sqrt (n:ℝ))).mono'
    (hκ.smul (continuous_vectorMeasureSpinMean_path μ β t ht sample).measurable).aestronglyMeasurable
  filter_upwards with q
  change ‖κ q •vectorMeasureSpinMean μ β t ht q sample‖≤K*Real.sqrt (n:ℝ)
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul (hB q) (norm_vectorMeasureGradient_le μ β t ht q sample.1
    (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample)) (norm_nonneg _) hK

theorem vectorMeasureKernelMean_component_eq (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K)
    (hB : ∀q,|κ q|≤K) (sample : VectorDisorderBrownianSample n) (i : Fin n) :
    vectorMeasureKernelMean μ s β t ht κ sample i=
      ∫q,κ q*vectorMeasureSpinMean μ β t ht q sample i ∂parisiFreeMeasure μ s := by
  have he:=(EuclideanSpace.proj i).integral_comp_comm
    (integrable_vectorMeasureKernelMean μ s β t ht κ hκ K hK hB sample)
  exact he.symm

theorem vectorMeasureKernelMean_component_bound (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (hs : s∈Icc (0:ℝ) 1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K)
    (sample : VectorDisorderBrownianSample n) (i : Fin n) :
    ‖vectorMeasureKernelMean μ s β t ht κ sample i‖≤K := by
  rw [vectorMeasureKernelMean_component_eq μ s β t ht κ hκ K hK hB]
  apply parisiFree_norm_integral_le μ s hs _ K hK
  intro q
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul (hB q)
    (vectorMeasureSpinMean_component_bound μ β t ht q sample i) (abs_nonneg _) hK

theorem integrable_vectorMeasureKernelOffset (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K)
    (hB : ∀q,|κ q|≤K) (sample : VectorDisorderBrownianSample n) :
    Integrable (fun q=>κ q*‖vectorMeasureSpinMean μ β t ht q sample‖^2/2) (parisiFreeMeasure μ s) := by
  apply (integrable_const (K*(n:ℝ)/2)).mono'
    ((hκ.mul ((continuous_vectorMeasureSpinMean_path μ β t ht sample).measurable.norm.pow_const 2)).div_const 2).aestronglyMeasurable
  filter_upwards with q
  change ‖κ q*‖vectorMeasureSpinMean μ β t ht q sample‖^2/2‖≤K*(n:ℝ)/2
  rw [norm_div,norm_mul,Real.norm_eq_abs (κ q),
    Real.norm_of_nonneg (sq_nonneg ‖vectorMeasureSpinMean μ β t ht q sample‖),Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul (hB q)
    (norm_sq_le_dimension_of_components _ (vectorMeasureSpinMean_component_bound μ β t ht q sample))
    (sq_nonneg _) hK

theorem vectorMeasureKernelOffset_bound (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (hs : s∈Icc (0:ℝ) 1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureKernelOffset μ s β t ht κ sample‖≤K*(n:ℝ)/2 := by
  unfold vectorMeasureKernelOffset
  apply parisiFree_norm_integral_le μ s hs _ _ (by positivity)
  intro q
  rw [norm_div,norm_mul,Real.norm_eq_abs (κ q),
    Real.norm_of_nonneg (sq_nonneg ‖vectorMeasureSpinMean μ β t ht q sample‖),Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul (hB q)
    (norm_sq_le_dimension_of_components _ (vectorMeasureSpinMean_component_bound μ β t ht q sample))
    (sq_nonneg _) hK

end QuantitativePaper
