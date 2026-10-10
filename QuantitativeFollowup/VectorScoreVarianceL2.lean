module
public import QuantitativeFollowup.VectorScoreVariance

@[expose] public section

/-! The actual weighted-score variance extends to every nonnegative L2
kernel. Truncation is dominated by the actual kernel, rather than by a
bound depending on the truncation level. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasureWeightedOverlapScore_nonneg_kernel_bound (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) (hκpos : ∀q,0≤κ q)
    (z : VectorDisorderBrownianSample n×Configuration n) :
    ‖vectorMeasureWeightedOverlapScore μ s β t ht κ z‖≤(3/2)*(∫q,κ q ∂parisiFreeMeasure μ s) := by
  have hi:=(hiκ.const_mul (3/2))
  have h:=norm_integral_le_of_norm_le (f:=fun q=>κ q*vectorMeasureOverlapScore μ β t ht q z) hi
    (.of_forall fun q=>by
      rw [norm_mul,Real.norm_of_nonneg (hκpos q)]
      have hb : ‖vectorMeasureOverlapScore μ β t ht q z‖≤3/2 := by
        simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht q z
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (hκpos q))
  simpa only [vectorMeasureWeightedOverlapScore,integral_const_mul] using h

theorem vector_weighted_score_variance_L2 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hκpos : ∀q,0≤κ q)
    (hL : MemLp κ 2 (parisiFreeMeasure μ s)) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ)
      (vectorMeasureSpinPathLaw μ β t s ht.le)≤
      (1/((n:ℝ)*((1-t)*β^2)))*(∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) := by
  let κj : ℕ→Paper.Overlap→ℝ:=fun j q=>min (κ q) (j:ℝ)
  have hiκ : Integrable κ (parisiFreeMeasure μ s):=hL.integrable one_le_two
  have hsq : Integrable (fun q=>κ q^2) (parisiFreeMeasure μ s):=hL.integrable_sq
  have hm (j : ℕ) : Measurable (κj j):=hκ.min measurable_const
  have hpos (j : ℕ) (q : Paper.Overlap) : 0≤κj j q:=le_min (hκpos q) (Nat.cast_nonneg j)
  have hle (j : ℕ) (q : Paper.Overlap) : κj j q≤κ q:=min_le_left _ _
  have hb (j : ℕ) (q : Paper.Overlap) : |κj j q|≤(j:ℝ):=by
    rw [abs_of_nonneg (hpos j q)]
    exact min_le_right _ _
  have hlim (q : Paper.Overlap) : Tendsto (fun j=>κj j q) atTop (𝓝 (κ q)) := by
    have he : ∀ᶠj : ℕ in atTop,κ q≤(j:ℝ):=(tendsto_natCast_atTop_atTop.eventually_ge_atTop (κ q))
    apply tendsto_const_nhds.congr'
    exact he.mono fun j hj=>by dsimp [κj];rw [min_eq_left hj]
  have hif (j : ℕ) : Integrable (κj j) (parisiFreeMeasure μ s):=
    hiκ.mono' (hm j).aestronglyMeasurable (.of_forall fun q=>by
      rw [Real.norm_of_nonneg (hpos j q)]
      exact hle j q)
  let C : ℝ:=(3/2)*(∫q,κ q ∂parisiFreeMeasure μ s)
  have hC : 0≤C:=mul_nonneg (by norm_num) (integral_nonneg hκpos)
  have hFbound (z : VectorDisorderBrownianSample n×Configuration n) :
      ‖vectorMeasureWeightedOverlapScore μ s β t ht.le κ z‖≤C:=
    vectorMeasureWeightedOverlapScore_nonneg_kernel_bound μ s β t ht.le κ hκ hiκ hκpos z
  have hFjbound (j : ℕ) (z : VectorDisorderBrownianSample n×Configuration n) :
      ‖vectorMeasureWeightedOverlapScore μ s β t ht.le (κj j) z‖≤C :=
    (vectorMeasureWeightedOverlapScore_nonneg_kernel_bound μ s β t ht.le (κj j) (hm j) (hif j) (hpos j) z).trans
      (mul_le_mul_of_nonneg_left (integral_mono (hif j) hiκ (hle j)) (by norm_num))
  have hFlim (z : VectorDisorderBrownianSample n×Configuration n) :
      Tendsto (fun j=>vectorMeasureWeightedOverlapScore μ s β t ht.le (κj j) z) atTop
        (𝓝 (vectorMeasureWeightedOverlapScore μ s β t ht.le κ z)) := by
    unfold vectorMeasureWeightedOverlapScore
    apply tendsto_integral_of_dominated_convergence (fun q=>(3/2)*κ q)
    · intro j
      have hscore : Measurable (fun q=>vectorMeasureOverlapScore μ β t ht.le q z):=
        (continuous_vectorMeasureOverlapScore_path μ β t ht.le z).measurable
      exact ((hm j).mul hscore).aestronglyMeasurable
    · exact hiκ.const_mul _
    · intro j
      exact .of_forall fun q=>by
        rw [norm_mul,Real.norm_of_nonneg (hpos j q)]
        have hc : ‖vectorMeasureOverlapScore μ β t ht.le q z‖≤3/2:=by
          simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht.le q z
        exact (mul_le_mul (hle j q) hc (norm_nonneg _) (hκpos q)).trans_eq (by ring)
    · exact .of_forall fun q=>(hlim q).mul tendsto_const_nhds
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht.le
  have hV:=tendsto_variance_of_uniform_bound (vectorMeasureSpinPathLaw μ β t s ht.le) _ _
    (fun j=>measurable_vectorMeasureWeightedOverlapScore μ s β t ht.le (κj j) (hm j))
    (measurable_vectorMeasureWeightedOverlapScore μ s β t ht.le κ hκ) C hC hFjbound hFbound (.of_forall hFlim)
  have hR : Tendsto (fun j=>∫q,(κj j q)^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) atTop
      (𝓝 (∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s)) := by
    apply tendsto_integral_of_dominated_convergence (fun q=>κ q^2/s)
    · intro j
      exact ((hm j).pow_const 2 |>.div ((Paper.parisiCDF_measurable μ).comp measurable_subtype_coe)).aestronglyMeasurable
    · exact hsq.div_const s
    · intro j
      exact .of_forall fun q=>by
        have hCDF:=scalarFloor_cdf_lower hμ q.property.1
        rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hs.1.trans_le hCDF).le)]
        exact div_le_div₀ (sq_nonneg (κ q))
          (pow_le_pow_left₀ (hpos j q) (hle j q) 2) hs.1 hCDF
    · exact .of_forall fun q=>(hlim q).pow 2 |>.div_const _
  apply le_of_tendsto_of_tendsto hV (hR.const_mul _)
  exact .of_forall fun j=>vector_weighted_score_variance hn μ s β t hβ ht hs hμ hmin
    (κj j) (hm j) (j:ℝ) (Nat.cast_nonneg j) (hb j)

end QuantitativeFollowup
