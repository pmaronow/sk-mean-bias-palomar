module
public import QuantitativeFollowup.VectorConditionalSelfOverlap
public import QuantitativeFollowup.VectorSupportContact
public import QuantitativeFollowup.VectorScoreVariance

@[expose] public section

/-! Actual first moments of marked overlap scores and their contact-centered
kernel averages. Integrable kernels need not be bounded for the mean identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integral_vectorMeasureOverlapScore_eq_half_mean (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    (∫z,vectorMeasureOverlapScore (n:=n) μ β t ht.le q z ∂vectorMeasureSpinPathLaw μ β t a ht.le)=
      vectorMeanOverlap (n:=n) μ β t a ht.le q/2 := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hM : Measurable (vectorMeasureSpinMean (n:=n) μ β t ht.le q):=
    (adapted_vectorMeasureSpinMean μ β t ht.le q).mono ((vectorBrownianFiltration n).le _) le_rfl
  have h:=condExp_vectorMeasureOverlapScore_same (n:=n) μ β t a hβ ht q
  calc
    _=∫z,(vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureOverlapScore μ β t ht.le q|
      vectorSpinPast n (q:ℝ).toNNReal] z ∂vectorMeasureSpinPathLaw μ β t a ht.le :=
        (integral_condExp (vectorSpinPast_le n _)).symm
    _=∫z,‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(2*(n:ℝ))
      ∂vectorMeasureSpinPathLaw μ β t a ht.le := integral_congr_ae h
    _=_ := by
      rw [integral_div,integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le _
        (hM.norm.pow_const 2)]
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      rw [integral_finsetSum _ (fun i _=>by
        simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht.le q q i)]
      unfold vectorMeanOverlap
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

def vectorKernelOverlapLevel (μ : Paper.ParisiMeasure) (s : ℝ) (κ : Paper.Overlap→ℝ) : ℝ:=
  ∫q,κ q*(q:ℝ) ∂parisiFreeMeasure μ s

def vectorCenteredKernelScore (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1)
    (κ : Paper.Overlap→ℝ) (z : VectorDisorderBrownianSample n×Configuration n) : ℝ:=
  vectorMeasureWeightedOverlapScore μ s β t ht κ z-vectorKernelOverlapLevel μ s κ/2

theorem integrable_vectorMeasure_kernel_score_product (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) :
    Integrable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      κ z.1*vectorMeasureOverlapScore μ β t ht z.1 z.2)
      ((parisiFreeMeasure μ s).prod (vectorMeasureSpinPathLaw μ β t a ht)) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hd:=(hiκ.norm.const_mul (3/2)).comp_fst (vectorMeasureSpinPathLaw (n:=n) μ β t a ht)
  apply hd.mono' ((hκ.comp measurable_fst).mul
    (measurable_uncurry_vectorMeasureOverlapScore μ β t ht)).aestronglyMeasurable
  exact .of_forall fun z=>by
    change ‖κ z.1*vectorMeasureOverlapScore μ β t ht z.1 z.2‖≤(3/2)*‖κ z.1‖
    rw [norm_mul]
    have hb : ‖vectorMeasureOverlapScore μ β t ht z.1 z.2‖≤3/2 := by
      simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht z.1 z.2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (norm_nonneg (κ z.1))

theorem integral_vectorMeasureWeightedOverlapScore (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) :
    (∫z,vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ z
      ∂vectorMeasureSpinPathLaw μ β t a ht.le)=
      ∫q,κ q*vectorMeanOverlap (n:=n) μ β t a ht.le q/2 ∂parisiFreeMeasure μ s := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hi:=integrable_vectorMeasure_kernel_score_product (n:=n) μ s β t a ht.le κ hκ hiκ
  unfold vectorMeasureWeightedOverlapScore
  rw [←integral_integral_swap (μ:=parisiFreeMeasure μ s) (ν:=vectorMeasureSpinPathLaw μ β t a ht.le)
    (f:=fun q z=>κ q*vectorMeasureOverlapScore μ β t ht.le q z) hi]
  apply integral_congr_ae
  exact .of_forall fun q=>by
    dsimp only
    rw [integral_const_mul,integral_vectorMeasureOverlapScore_eq_half_mean μ β t a hβ ht q]
    ring

theorem integral_vectorCenteredKernelScore_zero (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ (parisiFreeMeasure μ s)) :
    (∫z,vectorCenteredKernelScore (n:=n) μ s β t ht.le κ z ∂vectorMeasureSpinPathLaw μ β t s ht.le)=0 := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht.le
  have hi:=(integrable_vectorMeasure_kernel_score_product (n:=n) μ s β t s ht.le κ hκ hiκ).integral_prod_right
  change Integrable (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ)
    (vectorMeasureSpinPathLaw μ β t s ht.le) at hi
  have hc : vectorMeanOverlap (n:=n) μ β t s ht.le=ᵐ[parisiFreeMeasure μ s] fun q=>(q:ℝ) := by
    filter_upwards [(parisiFreeMeasure μ s).support_mem_ae] with q hq
    exact (vector_free_support_contact hn μ s ⟨hs.1.le,hs.2⟩ hμ β t s hβ ht hs.1.le hmin q hq).2
  unfold vectorCenteredKernelScore
  rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul,
    integral_vectorMeasureWeightedOverlapScore μ s β t s hβ ht κ hκ hiκ]
  have he : (∫q,κ q*vectorMeanOverlap (n:=n) μ β t s ht.le q/2 ∂parisiFreeMeasure μ s)=
      vectorKernelOverlapLevel μ s κ/2 := by
    unfold vectorKernelOverlapLevel
    rw [←integral_div]
    exact integral_congr_ae (hc.mono fun q hq=>by dsimp only;rw [hq])
  rw [he,sub_self]

theorem variance_vectorCenteredKernelScore (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) :
    variance (vectorCenteredKernelScore (n:=n) μ s β t ht κ)
      (vectorMeasureSpinPathLaw μ β t a ht)=
      variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht κ)
        (vectorMeasureSpinPathLaw μ β t a ht) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  exact variance_sub_const (measurable_vectorMeasureWeightedOverlapScore μ s β t ht κ hκ).aestronglyMeasurable _

end QuantitativeFollowup
