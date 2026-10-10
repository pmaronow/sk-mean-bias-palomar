module
public import QuantitativePaper.VectorScoreEnergyLimit
public import QuantitativePaper.VectorSupportSlope

@[expose] public section

/-! The genuine minimizing-profile weighted score variance bound for
continuous kernels, obtained from the actual posterior estimate and the
proved free-support Hessian contact inequality. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem continuous_vectorMeasureHessianEnergyExpectation (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    Continuous (fun q : Paper.Overlap=>∫sample : VectorDisorderBrownianSample n,
      vectorMeasureHessianEnergy μ β t ht q sample ∂vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply continuous_of_dominated (μ:=vectorMeasureDisorderTilt (n:=n) μ β t a)
    (bound:=fun _=>(n : ℝ)^3)
  · exact fun q=>(measurable_vectorMeasureHessianEnergy μ β t ht q).aestronglyMeasurable
  · intro q
    exact .of_forall fun sample=>by
      rw [Real.norm_of_nonneg (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).1]
      exact (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).2
  · exact integrable_const _
  · exact .of_forall fun sample=>continuous_vectorMeasureHessianEnergy_path μ β t ht sample

theorem vectorMeasureHessianEnergyExpectation_nonneg_le (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    0≤(∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht q sample
      ∂vectorMeasureDisorderTilt μ β t a) ∧
    (∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht q sample
      ∂vectorMeasureDisorderTilt μ β t a)≤(n : ℝ)^3 := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  refine ⟨integral_nonneg fun sample=>(vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).1,?_⟩
  have h:=integral_mono (integrable_vectorMeasureHessianEnergy μ β t a ht q)
    (integrable_const ((n : ℝ)^3)) fun sample=>(vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).2
  simpa only [integral_const,probReal_univ,one_smul] using h

theorem integrable_kernel_square_div_cdf (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : 0<s) (hμ : μ∈scalarFloor s) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K) :
    Integrable (fun q=>κ q^2/Paper.parisiCDF μ q) (parisiFreeMeasure μ s) := by
  apply (integrable_const (K^2/s)).mono'
    ((hκ.pow_const 2).div ((Paper.parisiCDF_monotone μ).measurable.comp measurable_subtype_coe)).aestronglyMeasurable
  exact .of_forall fun q=>by
    have hf:=parisiCDF_floor_at_overlap μ s hμ q
    dsimp only [Pi.div_apply,Pi.mul_apply,Function.comp_apply]
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hs.trans_le hf).le)]
    have hsq : κ q^2≤K^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (κ q)) (hB q) 2
    exact div_le_div₀ (sq_nonneg K) hsq hs hf

theorem integrable_score_energy_integrand (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (hs : 0<s) (hμ : μ∈scalarFloor s) (κ : Paper.Overlap→ℝ)
    (hκ : Measurable κ) (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K) :
    Integrable (fun q=>κ q^2*((∫sample : VectorDisorderBrownianSample n,
      vectorMeasureHessianEnergy μ β t ht q sample ∂vectorMeasureDisorderTilt μ β t s)/
        Paper.parisiCDF μ q)) (parisiFreeMeasure μ s) := by
  have hm:=((continuous_vectorMeasureHessianEnergyExpectation (n:=n) μ β t s ht).measurable).div
    ((Paper.parisiCDF_monotone μ).measurable.comp measurable_subtype_coe)
  apply (integrable_const (K^2*((n : ℝ)^3/s))).mono' ((hκ.pow_const 2).mul hm).aestronglyMeasurable
  exact .of_forall fun q=>by
    have hf:=parisiCDF_floor_at_overlap μ s hμ q
    have hE:=vectorMeasureHessianEnergyExpectation_nonneg_le (n:=n) μ β t s ht q
    dsimp only [Pi.div_apply,Pi.mul_apply,Function.comp_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg hE.1 (hs.trans_le hf).le))]
    exact mul_le_mul (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (κ q)) (hB q) 2)
      (div_le_div₀ (by positivity) hE.2 hs hf) (div_nonneg hE.1 (hs.trans_le hf).le) (sq_nonneg K)

theorem vectorMeasureScoreEnergyBudget_le_minimizer (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0 : ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K) :
    vectorMeasureScoreEnergyBudget (n:=n) μ s β t ht.le κ≤
      ((n : ℝ)/((1-t)*β^2))*(∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) := by
  rw [←integral_const_mul]
  apply integral_mono_ae (integrable_score_energy_integrand μ s β t ht.le hs.1 hμ κ hκ K hK hB)
    ((integrable_kernel_square_div_cdf μ s hs.1 hμ κ hκ K hK hB).const_mul _)
  filter_upwards [(parisiFreeMeasure μ s).support_mem_ae] with q hq
  have hE:=vector_free_support_hessian_energy_bound hn μ s ⟨hs.1.le,hs.2⟩ hμ β t s hβ ht hs.1.le hmin q hq
  have hf:=parisiCDF_floor_at_overlap μ s hμ q
  have h:=mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hE (hs.1.trans_le hf).le) (sq_nonneg (κ q))
  convert h using 1 <;> ring

theorem vector_weighted_score_variance_continuous (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0 : ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Continuous κ) (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ)
      (vectorMeasureSpinPathLaw μ β t s ht.le)≤
      (1/((n : ℝ)*((1-t)*β^2)))*(∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) := by
  have hV:=vectorMeasureWeightedOverlapScore_variance_le_energy hn μ s β t hβ ht
    ⟨hs.1,hs.2.le⟩ hμ κ hκ K hK hB
  have hE:=vectorMeasureScoreEnergyBudget_le_minimizer hn μ s β t hβ ht hs hμ hmin κ hκ.measurable K hK hB
  apply hV.trans
  have h:=div_le_div_of_nonneg_right hE (sq_nonneg (n : ℝ))
  convert h using 1
  have hn' : (n : ℝ)≠0:=by positivity
  have hc : (1-t)*β^2≠0:=mul_ne_zero (sub_ne_zero.mpr ht.ne') (pow_ne_zero _ hβ)
  field_simp

end QuantitativeFollowup
