module
public import QuantitativeFollowup.VectorScoreVarianceContinuous
public import FourPapersCommon.BoundedContinuousApproximation
public import FourPapersCommon.BoundedVarianceConvergence

@[expose] public section

/-! Actual weighted score variance for bounded Borel kernels.  Continuous
density is proved in L2, followed by bounded dominated passage under the
actual marked-spin law and the exact free Stieltjes measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem tendsto_weighted_score_of_bounded_kernel_ae (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κj : ℕ→Paper.Overlap→ℝ) (κ : Paper.Overlap→ℝ)
    (hm : ∀j,Measurable (κj j)) (K : ℝ) (hK : 0≤K) (hB : ∀j q,|κj j q|≤K)
    (hlim : ∀ᵐq ∂parisiFreeMeasure μ s,Tendsto (fun j=>κj j q) atTop (𝓝 (κ q)))
    (p : VectorDisorderBrownianSample n×Configuration n) :
    Tendsto (fun j=>vectorMeasureWeightedOverlapScore μ s β t ht (κj j) p) atTop
      (𝓝 (vectorMeasureWeightedOverlapScore μ s β t ht κ p)) := by
  unfold vectorMeasureWeightedOverlapScore
  apply tendsto_integral_of_dominated_convergence (fun _=>K*(3/2))
  · intro j
    have hh:=(measurable_uncurry_vectorMeasureOverlapScore (n:=n) μ β t ht).comp
      (measurable_id.prodMk (measurable_const (a:=p)))
    have hs : Measurable (fun q : Paper.Overlap=>vectorMeasureOverlapScore μ β t ht q p) := by
      simpa only [Function.comp_def,id_eq] using hh
    exact ((hm j).mul hs).aestronglyMeasurable
  · exact integrable_const _
  · exact fun j=>.of_forall fun q=>by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact mul_le_mul (hB j q) (vectorMeasureOverlapScore_bound μ β t ht q p) (abs_nonneg _) hK
  · exact hlim.mono fun q hq=>hq.mul tendsto_const_nhds

theorem tendsto_variance_weighted_score_of_bounded_kernel_ae (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (hs : s∈Icc (0 : ℝ) 1)
    (κj : ℕ→Paper.Overlap→ℝ) (κ : Paper.Overlap→ℝ)
    (hm : ∀j,Measurable (κj j)) (hκ : Measurable κ)
    (K : ℝ) (hK : 0≤K) (hB : ∀j q,|κj j q|≤K) (hBF : ∀q,|κ q|≤K)
    (hlim : ∀ᵐq ∂parisiFreeMeasure μ s,Tendsto (fun j=>κj j q) atTop (𝓝 (κ q))) :
    Tendsto (fun j=>variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht (κj j))
      (vectorMeasureSpinPathLaw μ β t s ht)) atTop
      (𝓝 (variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht κ)
        (vectorMeasureSpinPathLaw μ β t s ht))) := by
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht
  exact tendsto_variance_of_uniform_bound _ _ _
    (fun j=>measurable_vectorMeasureWeightedOverlapScore μ s β t ht (κj j) (hm j))
    (measurable_vectorMeasureWeightedOverlapScore μ s β t ht κ hκ) (K*(3/2)) (by positivity)
    (fun j=>vectorMeasureWeightedOverlapScore_bound μ s β t ht hs (κj j) K hK (hB j))
    (vectorMeasureWeightedOverlapScore_bound μ s β t ht hs κ K hK hBF)
    (.of_forall (tendsto_weighted_score_of_bounded_kernel_ae μ s β t ht κj κ hm K hK hB hlim))

theorem vector_weighted_score_variance (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0 : ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ)
      (vectorMeasureSpinPathLaw μ β t s ht.le)≤
      (1/((n : ℝ)*((1-t)*β^2)))*(∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) := by
  obtain ⟨κj,hcont,hbound,hlim⟩:=exists_continuous_bounded_ae_approximation
    (parisiFreeMeasure μ s) κ hκ K hK hB
  have hR : Tendsto (fun j=>∫q,(κj j q)^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) atTop
      (𝓝 (∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s)) := by
    apply tendsto_integral_of_dominated_convergence (fun _=>K^2/s)
    · exact fun j=>((hcont j).measurable.pow_const 2 |>.div
        ((Paper.parisiCDF_monotone μ).measurable.comp measurable_subtype_coe)).aestronglyMeasurable
    · exact integrable_const _
    · intro j
      exact .of_forall fun q=>by
        have hf:=parisiCDF_floor_at_overlap μ s hμ q
        rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hs.1.trans_le hf).le)]
        have hsq : κj j q^2≤K^2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (κj j q)) (hbound j q) 2
        exact div_le_div₀ (sq_nonneg K) hsq hs.1 hf
    · exact hlim.mono fun q hq=>(hq.pow 2).div_const _
  apply le_of_tendsto_of_tendsto
    (tendsto_variance_weighted_score_of_bounded_kernel_ae μ s β t ht.le ⟨hs.1.le,hs.2.le⟩
      κj κ (fun j=>(hcont j).measurable) hκ K hK hbound hB hlim)
    (hR.const_mul _)
  exact .of_forall fun j=>vector_weighted_score_variance_continuous hn μ s β t hβ ht hs hμ hmin
    (κj j) (hcont j) K hK (hbound j)

end QuantitativeFollowup
