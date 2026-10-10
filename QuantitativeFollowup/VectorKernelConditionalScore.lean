module
public import QuantitativeFollowup.VectorScoreConditional

@[expose] public section

/-! Actual conditional scores of bounded past-supported Borel kernels.
The kernel may cover only a part of an atom of the free overlap measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem condExp_vectorMeasureWeightedOverlapScore_past (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Icc (0:ℝ) 1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K)
    (hB : ∀p,|κ p|≤K) (q : Paper.Overlap)
    (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→p≤q) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureWeightedOverlapScore μ s β t ht.le κ|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>(inner ℝ (vectorMeasureKernelMean μ s β t ht.le κ z.1)
        (vectorMeasureSpinMean μ β t ht.le q z.1)-vectorMeasureKernelOffset μ s β t ht.le κ z.1)/(n:ℝ) := by
  have hmean:=adapted_vectorMeasureKernelMean (n:=n) μ s β t ht.le κ hκ q hSupport
  have hoff:=adapted_vectorMeasureKernelOffset (n:=n) μ s β t ht.le κ hκ q hSupport
  have hb (i : Fin n) : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>vectorMeasureKernelMean μ s β t ht.le κ sample i):=
    (EuclideanSpace.proj i).continuous.measurable.comp hmean.measurable
  have h:=condExp_vectorMeasure_past_affine_score μ β t a hβ ht q
    (vectorMeasureKernelMean μ s β t ht.le κ) (vectorMeasureKernelOffset μ s β t ht.le κ)
    hb hoff.measurable K (K*(n:ℝ)/2) hK
    (fun sample i=>vectorMeasureKernelMean_component_bound μ s β t ht.le hs κ hκ K hK hB sample i)
    (vectorMeasureKernelOffset_bound μ s β t ht.le hs κ hκ K hK hB)
  have he : vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ=
      vectorMeasurePastAffineSpinScore (vectorMeasureKernelMean μ s β t ht.le κ)
        (vectorMeasureKernelOffset μ s β t ht.le κ) := by
    funext z
    exact vectorMeasureWeightedOverlapScore_eq_affine μ s β t ht.le κ hκ K hK hB z
  rw [he]
  exact h

theorem vectorMeasureKernelMean_inner_eq_integral (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (K : ℝ) (hK : 0≤K) (hB : ∀p,|κ p|≤K) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) :
    inner ℝ (vectorMeasureKernelMean μ s β t ht κ sample) (vectorMeasureSpinMean μ β t ht q sample)=
      ∫p,κ p*inner ℝ (vectorMeasureSpinMean μ β t ht p sample) (vectorMeasureSpinMean μ β t ht q sample)
        ∂parisiFreeMeasure μ s := by
  have hi:=integrable_vectorMeasureKernelMean μ s β t ht κ hκ K hK hB sample
  have h:=(innerSL ℝ (vectorMeasureSpinMean μ β t ht q sample)).integral_comp_comm hi
  simp only [innerSL_apply_apply,inner_smul_right,smul_eq_mul] at h
  simpa only [vectorMeasureKernelMean,real_inner_comm,mul_comm] using h.symm

theorem condExp_vectorMeasureWeightedOverlapScore_past_integral (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Icc (0:ℝ) 1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K)
    (hB : ∀p,|κ p|≤K) (q : Paper.Overlap)
    (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→p≤q) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureWeightedOverlapScore μ s β t ht.le κ|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>∫p,κ p*(‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2-
        ‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2)/(2*(n:ℝ))
        ∂parisiFreeMeasure μ s := by
  have h:=condExp_vectorMeasureWeightedOverlapScore_past (n:=n) μ s β t a hβ ht hs κ hκ K hK hB q hSupport
  filter_upwards [h] with z hz
  rw [hz,vectorMeasureKernelMean_inner_eq_integral μ s β t ht.le κ hκ K hK hB q z.1]
  have hi:=(innerSL ℝ (vectorMeasureSpinMean μ β t ht.le q z.1)).integrable_comp
    (integrable_vectorMeasureKernelMean μ s β t ht.le κ hκ K hK hB z.1)
  simp only [innerSL_apply_apply,inner_smul_right,smul_eq_mul] at hi
  have hi' : Integrable (fun p=>κ p*inner ℝ (vectorMeasureSpinMean μ β t ht.le p z.1)
      (vectorMeasureSpinMean μ β t ht.le q z.1)) (parisiFreeMeasure μ s) := by
    simpa only [real_inner_comm] using hi
  have ho:=integrable_vectorMeasureKernelOffset μ s β t ht.le κ hκ K hK hB z.1
  unfold vectorMeasureKernelOffset
  rw [←integral_sub hi' ho,←integral_div]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    dsimp only
    rw [norm_sub_sq_real,real_inner_comm (vectorMeasureSpinMean μ β t ht.le q z.1)
      (vectorMeasureSpinMean μ β t ht.le p z.1)]
    ring

end QuantitativeFollowup
