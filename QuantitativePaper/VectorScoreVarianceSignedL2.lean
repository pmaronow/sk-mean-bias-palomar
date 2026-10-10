module
public import QuantitativeFollowup.VectorScoreVarianceL2

@[expose] public section

/-! The literal integrated covariance variance estimate for every signed
L2 kernel. Actual clipped kernels converge under the genuine marked-spin
law, with a common integrable-kernel bound independent of clipping level. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
open QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def signedKernelTruncation (κ : Paper.Overlap→ℝ) (j : ℕ) (q : Paper.Overlap) : ℝ :=
  max (-(j:ℝ)) (min (κ q) (j:ℝ))

theorem measurable_signedKernelTruncation (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (j : ℕ) :
    Measurable (signedKernelTruncation κ j) := measurable_const.max (hκ.min measurable_const)

theorem signedKernelTruncation_abs_le_level (κ : Paper.Overlap→ℝ) (j : ℕ) (q : Paper.Overlap) :
    |signedKernelTruncation κ j q|≤(j:ℝ) := by
  apply abs_le.mpr
  refine ⟨le_max_left _ _,max_le ?_ (min_le_right _ _)⟩
  linarith [Nat.cast_nonneg (α:=ℝ) j]

theorem signedKernelTruncation_abs_le (κ : Paper.Overlap→ℝ) (j : ℕ) (q : Paper.Overlap) :
    |signedKernelTruncation κ j q|≤|κ q| := by
  unfold signedKernelTruncation
  apply abs_le.mpr
  refine ⟨(le_min (neg_abs_le _) ?_).trans (le_max_right _ _),max_le ?_ ((min_le_left _ _).trans (le_abs_self _))⟩
  · linarith [abs_nonneg (κ q),Nat.cast_nonneg (α:=ℝ) j]
  · linarith [abs_nonneg (κ q),Nat.cast_nonneg (α:=ℝ) j]

theorem tendsto_signedKernelTruncation (κ : Paper.Overlap→ℝ) (q : Paper.Overlap) :
    Tendsto (fun j=>signedKernelTruncation κ j q) atTop (𝓝 (κ q)) := by
  have hge : ∀ᶠj:ℕ in atTop,|κ q|≤(j:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  apply tendsto_const_nhds.congr'
  filter_upwards [hge] with j hj
  unfold signedKernelTruncation
  rw [min_eq_left ((le_abs_self _).trans hj),max_eq_right (by linarith [neg_abs_le (κ q)])]

theorem vectorMeasureWeightedOverlapScore_integrable_kernel_bound (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (z : VectorDisorderBrownianSample n×Configuration n) :
    ‖vectorMeasureWeightedOverlapScore μ s β t ht κ z‖≤
      (3/2)*(∫q,|κ q| ∂parisiFreeMeasure μ s) := by
  have hh := norm_integral_le_of_norm_le
    (f:=fun q=>κ q*vectorMeasureOverlapScore μ β t ht q z) (hiκ.norm.const_mul (3/2))
    (.of_forall fun q=>by
      rw [norm_mul,Real.norm_eq_abs]
      have hb : ‖vectorMeasureOverlapScore μ β t ht q z‖≤3/2 := by
        simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht q z
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg _))
  simpa only [vectorMeasureWeightedOverlapScore,integral_const_mul,Real.norm_eq_abs] using hh

/-- The source kernel may have either sign. Its actual L2 hypothesis
discharges all marked-law and coefficient-integral convergence inputs. -/
theorem vector_weighted_score_variance_signed_L2 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hL : MemLp κ 2 (parisiFreeMeasure μ s)) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ)
      (vectorMeasureSpinPathLaw μ β t s ht.le)≤
      (1/((n:ℝ)*((1-t)*β^2)))*(∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) := by
  let κj:=signedKernelTruncation κ
  have hiκ : Integrable κ (parisiFreeMeasure μ s) := hL.integrable one_le_two
  have hsq : Integrable (fun q=>κ q^2) (parisiFreeMeasure μ s) := hL.integrable_sq
  have hm (j:ℕ) : Measurable (κj j) := measurable_signedKernelTruncation κ hκ j
  have hif (j:ℕ) : Integrable (κj j) (parisiFreeMeasure μ s) :=
    hiκ.norm.mono' (hm j).aestronglyMeasurable (.of_forall fun q=>by
      simpa only [Real.norm_eq_abs] using signedKernelTruncation_abs_le κ j q)
  let C : ℝ := (3/2)*(∫q,|κ q| ∂parisiFreeMeasure μ s)
  have hC : 0≤C := mul_nonneg (by norm_num) (integral_nonneg fun q=>abs_nonneg _)
  have hFbound (z : VectorDisorderBrownianSample n×Configuration n) :
      ‖vectorMeasureWeightedOverlapScore μ s β t ht.le κ z‖≤C :=
    vectorMeasureWeightedOverlapScore_integrable_kernel_bound μ s β t ht.le κ hiκ z
  have hFjbound (j:ℕ) (z : VectorDisorderBrownianSample n×Configuration n) :
      ‖vectorMeasureWeightedOverlapScore μ s β t ht.le (κj j) z‖≤C :=
    (vectorMeasureWeightedOverlapScore_integrable_kernel_bound μ s β t ht.le (κj j) (hif j) z).trans
      (mul_le_mul_of_nonneg_left (integral_mono (hif j).abs hiκ.abs
        (signedKernelTruncation_abs_le κ j)) (by norm_num))
  have hFlim (z : VectorDisorderBrownianSample n×Configuration n) :
      Tendsto (fun j=>vectorMeasureWeightedOverlapScore μ s β t ht.le (κj j) z) atTop
        (𝓝 (vectorMeasureWeightedOverlapScore μ s β t ht.le κ z)) := by
    unfold vectorMeasureWeightedOverlapScore
    apply tendsto_integral_of_dominated_convergence (fun q=>(3/2)*|κ q|)
    · intro j
      exact ((hm j).mul (continuous_vectorMeasureOverlapScore_path μ β t ht.le z).measurable).aestronglyMeasurable
    · exact hiκ.abs.const_mul _
    · intro j
      exact .of_forall fun q=>by
        rw [norm_mul,Real.norm_eq_abs]
        have hc : ‖vectorMeasureOverlapScore μ β t ht.le q z‖≤3/2 := by
          simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht.le q z
        exact (mul_le_mul (signedKernelTruncation_abs_le κ j q) hc (norm_nonneg _) (abs_nonneg _)).trans_eq (by ring)
    · exact .of_forall fun q=>(tendsto_signedKernelTruncation κ q).mul tendsto_const_nhds
  let := vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht.le
  have hV := tendsto_variance_of_uniform_bound (vectorMeasureSpinPathLaw μ β t s ht.le) _ _
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
        have hCDF := scalarFloor_cdf_lower hμ q.property.1
        rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hs.1.trans_le hCDF).le)]
        have hjq : (κj j q)^2≤(κ q)^2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (signedKernelTruncation_abs_le κ j q) 2
        exact div_le_div₀ (sq_nonneg _) hjq hs.1 hCDF
    · exact .of_forall fun q=>(tendsto_signedKernelTruncation κ q).pow 2 |>.div_const _
  apply le_of_tendsto_of_tendsto hV (hR.const_mul _)
  exact .of_forall fun j=>vector_weighted_score_variance hn μ s β t hβ ht hs hμ hmin
    (κj j) (hm j) (j:ℝ) (Nat.cast_nonneg j) (signedKernelTruncation_abs_le_level κ j)

/-- The conclusion is intrinsic to L2: an everywhere Borel representative
is constructed from its actual a.e. measurable class, rather than assumed. -/
theorem vector_weighted_score_variance_memLp (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hL : MemLp κ 2 (parisiFreeMeasure μ s)) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ)
      (vectorMeasureSpinPathLaw μ β t s ht.le)≤
      (1/((n:ℝ)*((1-t)*β^2)))*(∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) := by
  let η:=hL.aestronglyMeasurable.mk κ
  have he : κ=ᵐ[parisiFreeMeasure μ s] η := hL.aestronglyMeasurable.ae_eq_mk
  have hm : Measurable η := hL.aestronglyMeasurable.measurable_mk
  have hη : MemLp η 2 (parisiFreeMeasure μ s) := (memLp_congr_ae he).mp hL
  have hscore : vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ=
      vectorMeasureWeightedOverlapScore μ s β t ht.le η := by
    funext z
    unfold vectorMeasureWeightedOverlapScore
    apply integral_congr_ae
    exact he.mono fun q hq=>by dsimp only;rw [hq]
  have hint : (∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s)=
      (∫q,η q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s) := by
    apply integral_congr_ae
    exact he.mono fun q hq=>by dsimp only;rw [hq]
  rw [hscore,hint]
  exact vector_weighted_score_variance_signed_L2 hn μ s β t hβ ht hs hμ hmin η hm hη

end QuantitativePaper
