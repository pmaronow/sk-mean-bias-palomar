module
public import QuantitativeFollowup.VectorConditionalSelfOverlap
public import FourPapersCommon.ConditionalKernelComparison

@[expose] public section

/-! The later-window conditional comparison for the actual self-overlap.
Deterministic Borel kernels include the normalized partial-atom windows. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasureWeightedOverlapScore_future_comparison_of_integrable (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (hκpos : ∀p,0≤κ p) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→q≤p) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ))
      ≤ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
    (fun z=>2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureWeightedOverlapScore μ s β t ht.le κ|
      vectorSpinPast n (q:ℝ).toNNReal] z)) := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=inferInstance
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let m:=vectorSpinPast n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=ambient
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hM : StronglyMeasurable[m] (fun z : VectorDisorderBrownianSample n×Configuration n=>
      vectorMeasureSpinMean μ β t ht.le q z.1):=
    (adapted_vectorMeasureSpinMean μ β t ht.le q).stronglyMeasurable.comp_measurable
      (comap_measurable Prod.fst)
  have hS : StronglyMeasurable[m] (fun z : VectorDisorderBrownianSample n×Configuration n=>
      ‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ)) := by
    have h:=(hM.norm.pow 2).mul
      (stronglyMeasurable_const : StronglyMeasurable[m]
        (fun _z : VectorDisorderBrownianSample n×Configuration n=>(n:ℝ)⁻¹))
    convert h using 1
    funext z
    simp only [div_eq_mul_inv,Pi.mul_apply,Pi.pow_apply]
  have hiS : Integrable (fun z : VectorDisorderBrownianSample n×Configuration n=>
      ‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ)) J := by
    apply (integrable_const (1:ℝ)).mono' (hS.mono (vectorSpinPast_le n _)).aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [Real.norm_of_nonneg (by positivity)]
      exact (div_le_one₀ (Nat.cast_pos.mpr hn)).mpr (norm_sq_le_dimension_of_components _
        (vectorMeasureSpinMean_component_bound μ β t ht.le q z.1))
  have hcompare : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→
      (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ))
      ≤ᵐ[J]fun z=>2*J[(vectorMeasureOverlapScore μ β t ht.le p)|m] z := by
    filter_upwards [hSupport] with p hp
    exact fun hz=>vectorMeasureOverlapScore_future_comparison μ β t a hβ ht (hp hz)
  exact conditional_kernel_comparison_of_integrable J (parisiFreeMeasure μ s) m (vectorSpinPast_le n _)
    _ hS hiS (fun z=>vectorMeasureOverlapScore μ β t ht.le z.1 z.2)
    (measurable_uncurry_vectorMeasureOverlapScore μ β t ht.le) (3/2) (by norm_num)
    (fun z=>by simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht.le z.1 z.2)
    κ hκ hiκ hκpos hnormal hcompare

theorem vectorMeasureWeightedOverlapScore_future_comparison (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K)
    (hB : ∀p,|κ p|≤K) (hκpos : ∀p,0≤κ p) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→q≤p) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ))
      ≤ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
    (fun z=>2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureWeightedOverlapScore μ s β t ht.le κ|
      vectorSpinPast n (q:ℝ).toNNReal] z)) := by
  apply vectorMeasureWeightedOverlapScore_future_comparison_of_integrable hn μ s β t a hβ ht κ hκ
    _ hκpos hnormal q hSupport
  exact (integrable_const K).mono' hκ.aestronglyMeasurable
    (.of_forall fun p=>by simpa only [Real.norm_eq_abs] using hB p)

end QuantitativeFollowup
