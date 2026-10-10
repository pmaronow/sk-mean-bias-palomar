module
public import QuantitativeFollowup.VectorKernelConditionalScore

@[expose] public section

/-! The earlier-window conditional comparison with its exact nonnegative
mean-increment residual, under the actual physical marked-spin law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem norm_sq_vectorMeasureSpinMean_sub_le (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (p q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureSpinMean μ β t ht q sample-vectorMeasureSpinMean μ β t ht p sample‖^2≤4*(n:ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _≤∑_i : Fin n,(4:ℝ) := Finset.sum_le_sum fun i _=>by
      have hp:=abs_le.mp (vectorMeasureSpinMean_component_bound μ β t ht p sample i)
      have hq:=abs_le.mp (vectorMeasureSpinMean_component_bound μ β t ht q sample i)
      simp only [PiLp.sub_apply]
      nlinarith
    _=4*(n:ℝ) := by simp;ring

theorem vectorMeasureWeightedOverlapScore_past_comparison (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Icc (0:ℝ) 1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K)
    (hB : ∀p,|κ p|≤K) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1) (q : Paper.Overlap)
    (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→p≤q) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ))
      =ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
    (fun z=>2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureWeightedOverlapScore μ s β t ht.le κ|
        vectorSpinPast n (q:ℝ).toNNReal] z)+
      (∫p,κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2
        ∂parisiFreeMeasure μ s)/(n:ℝ)) := by
  have hiκ : Integrable κ (parisiFreeMeasure μ s):=
    (integrable_const K).mono' hκ.aestronglyMeasurable
      (.of_forall fun p=>by simpa only [Real.norm_eq_abs] using hB p)
  have h:=condExp_vectorMeasureWeightedOverlapScore_past_integral (n:=n) μ s β t a hβ ht hs κ hκ K hK hB q hSupport
  filter_upwards [h] with z hz
  have hm : Measurable (fun p : Paper.Overlap=>vectorMeasureSpinMean μ β t ht.le p z.1):=
    (continuous_vectorMeasureSpinMean_path μ β t ht.le z.1).measurable
  have hiR : Integrable (fun p=>κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-
      vectorMeasureSpinMean μ β t ht.le p z.1‖^2) (parisiFreeMeasure μ s) := by
    apply (integrable_const (K*(4*(n:ℝ)))).mono'
      (hκ.mul ((measurable_const.sub hm).norm.pow_const 2)).aestronglyMeasurable
    exact .of_forall fun p=>by
      change ‖κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-
        vectorMeasureSpinMean μ β t ht.le p z.1‖^2‖≤K*(4*(n:ℝ))
      rw [norm_mul,Real.norm_eq_abs (κ p),Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (hB p) (norm_sq_vectorMeasureSpinMean_sub_le μ β t ht.le p q z.1)
        (sq_nonneg _) hK
  have hiC : Integrable (fun p=>κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2)
      (parisiFreeMeasure μ s):=hiκ.mul_const _
  have he : (∫p,κ p*(‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2-
        ‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2)/(2*(n:ℝ))
      ∂parisiFreeMeasure μ s)=
      (‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2-
        ∫p,κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2
          ∂parisiFreeMeasure μ s)/(2*(n:ℝ)) := by
    rw [integral_div]
    simp_rw [mul_sub]
    rw [integral_sub hiC hiR,integral_mul_const,hnormal,one_mul]
  change _=2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureWeightedOverlapScore μ s β t ht.le κ|
    vectorSpinPast n (q:ℝ).toNNReal] z)+_
  rw [hz,he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end QuantitativeFollowup
