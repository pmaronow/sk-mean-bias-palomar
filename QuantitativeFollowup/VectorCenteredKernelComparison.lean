module
public import QuantitativeFollowup.VectorPastIntegrableKernelComparison
public import QuantitativeFollowup.VectorFutureKernelComparison
public import QuantitativeFollowup.VectorScoreVarianceL2

@[expose] public section

/-! Literal centered two-sided conditional comparison of Lemma 3.1.
Kernels are arbitrary nonnegative normalized integrable Borel functions;
no bounded-kernel restriction remains. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem condExp_vectorCenteredKernelScore (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) (q : Paper.Overlap) :
    (vectorMeasureSpinPathLaw μ β t a ht)[vectorCenteredKernelScore (n:=n) μ s β t ht κ|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht]
      fun z=>(vectorMeasureSpinPathLaw μ β t a ht)[vectorMeasureWeightedOverlapScore μ s β t ht κ|
        vectorSpinPast n (q:ℝ).toNNReal] z-vectorKernelOverlapLevel μ s κ/2 := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hi:=(integrable_vectorMeasure_kernel_score_product (n:=n) μ s β t a ht κ hκ hiκ).integral_prod_right
  change Integrable (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht κ)
    (vectorMeasureSpinPathLaw μ β t a ht) at hi
  have he:=condExp_sub hi (integrable_const (vectorKernelOverlapLevel μ s κ/2))
    (vectorSpinPast n (q:ℝ).toNNReal)
  have hc:=condExp_const (μ:=vectorMeasureSpinPathLaw μ β t a ht) (vectorSpinPast_le n (q:ℝ).toNNReal)
    (vectorKernelOverlapLevel μ s κ/2)
  filter_upwards [he] with z hz
  change (vectorMeasureSpinPathLaw μ β t a ht)[vectorCenteredKernelScore μ s β t ht κ|
    vectorSpinPast n (q:ℝ).toNNReal] z=_ at hz
  simpa only [Pi.sub_apply,hc] using hz

theorem vectorCenteredKernelScore_future_comparison (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (hκpos : ∀p,0≤κ p) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→q≤p) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ)-(q:ℝ))
      ≤ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
    (fun z=>(vectorKernelOverlapLevel μ s κ-(q:ℝ))+
      2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorCenteredKernelScore μ s β t ht.le κ|
        vectorSpinPast n (q:ℝ).toNNReal] z)) := by
  have h:=vectorMeasureWeightedOverlapScore_future_comparison_of_integrable hn μ s β t a hβ ht κ hκ hiκ
    hκpos hnormal q hSupport
  have hc:=condExp_vectorCenteredKernelScore (n:=n) μ s β t a ht.le κ hκ hiκ q
  filter_upwards [h,hc] with z hz hc
  try dsimp only at *
  rw [hc]
  linarith

theorem vectorCenteredKernelScore_past_comparison (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (hκpos : ∀p,0≤κ p) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→p≤q) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ)-(q:ℝ))
      =ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
    (fun z=>(vectorKernelOverlapLevel μ s κ-(q:ℝ))+
      2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorCenteredKernelScore μ s β t ht.le κ|
        vectorSpinPast n (q:ℝ).toNNReal] z)+
      (∫p,κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2
        ∂parisiFreeMeasure μ s)/(n:ℝ)) := by
  have h:=vectorMeasureWeightedOverlapScore_past_comparison_of_integrable (n:=n) μ s β t a hβ ht κ hκ hiκ
    hκpos hnormal q hSupport
  have hc:=condExp_vectorCenteredKernelScore (n:=n) μ s β t a ht.le κ hκ hiκ q
  filter_upwards [h,hc] with z hz hc
  try dsimp only at *
  rw [hc]
  linarith

theorem vectorCenteredKernelScore_past_lower_comparison (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (hκpos : ∀p,0≤κ p) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→p≤q) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>(vectorKernelOverlapLevel μ s κ-(q:ℝ))+
      2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorCenteredKernelScore μ s β t ht.le κ|
        vectorSpinPast n (q:ℝ).toNNReal] z))≤ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
    (fun z=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ)-(q:ℝ)) := by
  have h:=vectorCenteredKernelScore_past_comparison (n:=n) μ s β t a hβ ht κ hκ hiκ hκpos hnormal q hSupport
  filter_upwards [h] with z hz
  try dsimp only at *
  have hr : 0≤(∫p,κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2
        ∂parisiFreeMeasure μ s)/(n:ℝ):=
    div_nonneg (integral_nonneg fun p=>mul_nonneg (hκpos p) (sq_nonneg _)) (Nat.cast_nonneg n)
  linarith

theorem vectorCenteredKernelScore_conditional_square_variance (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hκpos : ∀p,0≤κ p)
    (hL : MemLp κ 2 (parisiFreeMeasure μ s)) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) :
    (∫z,((vectorMeasureSpinPathLaw μ β t s ht.le)[vectorCenteredKernelScore (n:=n) μ s β t ht.le κ|
      vectorSpinPast n (q:ℝ).toNNReal] z)^2 ∂vectorMeasureSpinPathLaw μ β t s ht.le)≤
      variance (vectorCenteredKernelScore (n:=n) μ s β t ht.le κ) (vectorMeasureSpinPathLaw μ β t s ht.le) ∧
    variance (vectorCenteredKernelScore (n:=n) μ s β t ht.le κ) (vectorMeasureSpinPathLaw μ β t s ht.le)≤
      (1/((n:ℝ)*((1-t)*β^2)))*(∫p,κ p^2/Paper.parisiCDF μ p ∂parisiFreeMeasure μ s) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht.le
  have hiκ:=hL.integrable one_le_two
  have hF : MemLp (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ) 2 J:=
    MemLp.of_bound (measurable_vectorMeasureWeightedOverlapScore μ s β t ht.le κ hκ).aestronglyMeasurable (3/2)
      (.of_forall fun z=>by simpa only [hnormal,mul_one] using
        vectorMeasureWeightedOverlapScore_nonneg_kernel_bound μ s β t ht.le κ hκ hiκ hκpos z)
  have hΛ : MemLp (vectorCenteredKernelScore (n:=n) μ s β t ht.le κ) 2 J:=hF.sub (memLp_const _)
  have he:=integral_vectorCenteredKernelScore_zero hn μ s β t hβ ht hs hμ hmin κ hκ hiκ
  have hsq:=square_condExp_le_condExp_square J (vectorSpinPast n (q:ℝ).toNNReal) (vectorSpinPast_le n _)
    (vectorCenteredKernelScore μ s β t ht.le κ) hΛ
  have hc:=integral_mono_ae (hΛ.condExp one_le_two).integrable_sq integrable_condExp hsq
  rw [integral_condExp (vectorSpinPast_le n _)] at hc
  refine ⟨?_,?_⟩
  · have hv:=variance_eq_sub hΛ
    change (∫ z, vectorCenteredKernelScore (n:=n) μ s β t ht.le κ z ∂J)=0 at he
    simp only [Pi.pow_apply] at hv
    rw [he] at hv
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at hv
    rw [hv]
    simpa only [Pi.pow_apply] using hc
  · rw [variance_vectorCenteredKernelScore μ s β t s ht.le κ hκ]
    exact vector_weighted_score_variance_L2 hn μ s β t hβ ht hs hμ hmin κ hκ hκpos hL

end QuantitativeFollowup
