module
public import QuantitativePaper.VectorMeasureOverlapScore
public import QuantitativePaper.VectorMeasureAffineScoreConditionalVariance
public import QuantitativeFollowup.VectorScoreTail

@[expose] public section

/-! Exact conditional mean, conditional variance, and total variance of the
literal normalized terminal-spin score under the actual marked law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativeFollowup
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem memLp_vectorMeasureOverlapScore (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    MemLp (vectorMeasureOverlapScore (n:=n) μ β t ht q) 2
      (vectorMeasureSpinPathLaw μ β t a ht) := by
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  exact MemLp.of_bound (measurable_vectorMeasureOverlapScore μ β t ht q).aestronglyMeasurable
    (3/2) (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using
      vectorMeasureOverlapScore_bound μ β t ht q z)

theorem condExp_vectorMeasureOverlapScore (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureOverlapScore (n:=n) μ β t ht.le q|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>vectorSelfOverlap μ β t ht.le q z/2 := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=inferInstance
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let V:=vectorSpinPast n (q:ℝ).toNNReal
  let B : Fin n→(VectorDisorderBrownianSample n×Configuration n)→ℝ:=fun i z=>
    vectorMeasureSpinMean μ β t ht.le q z.1 i
  let X : Fin n→(VectorDisorderBrownianSample n×Configuration n)→ℝ:=fun i z=>Paper.spinSign (z.2 i)
  let d:=fun z : VectorDisorderBrownianSample n×Configuration n=>
    ‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/2
  letI : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=ambient
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hB (i : Fin n) : StronglyMeasurable[V] (B i):=
    (adapted_vectorMeasureSpinMean_joint μ β t ht.le q i).stronglyMeasurable
  have hX (i : Fin n) : Measurable (X i):=
    (measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i))).comp measurable_snd
  have hBb (i : Fin n) (z : VectorDisorderBrownianSample n×Configuration n) : ‖B i z‖≤1:=by
    simpa only [Real.norm_eq_abs] using vectorMeasureSpinMean_component_bound μ β t ht.le q z.1 i
  have hXb (i : Fin n) (z : VectorDisorderBrownianSample n×Configuration n) : ‖X i z‖≤1:=by
    simp [X,Real.norm_eq_abs,Paper.abs_spinSign]
  have hlin:=condExp_bounded_random_linear (P:=J) V (vectorSpinPast_le n _) B X hB hX 1 zero_le_one hBb hXb
  have hdknown : StronglyMeasurable[V] d := by
    letI : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=V
    exact ((((adapted_vectorMeasureSpinMean μ β t ht.le q).comp
      (comap_measurable Prod.fst)).norm.pow_const 2).div_const 2).stronglyMeasurable
  have hdi : Integrable d J := by
    apply bounded_real_integrable _ (hdknown.mono (vectorSpinPast_le n _)).measurable ((n:ℝ)/2)
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (norm_sq_le_dimension_of_components _
      (fun i=>vectorMeasureSpinMean_component_bound μ β t ht.le q z.1 i)) (by norm_num)
  have hli : Integrable (fun z=>∑i,B i z*X i z) J := by
    apply bounded_real_integrable _ (Finset.measurable_sum _ fun i _=>
      ((hB i).mono (vectorSpinPast_le n _)).measurable.mul (hX i)) (n:ℝ)
    intro z
    calc
      _≤∑i : Fin n,‖B i z*X i z‖:=norm_sum_le _ _
      _≤∑_i : Fin n,(1:ℝ):=Finset.sum_le_sum fun i _=>by
        rw [norm_mul]
        exact (mul_le_mul (hBb i z) (hXb i z) (norm_nonneg _) zero_le_one).trans_eq (by ring)
      _=_:=by simp
  have hsub:=condExp_sub hli hdi V
  have hdc:=condExp_of_stronglyMeasurable (vectorSpinPast_le n _) hdknown hdi
  have hs:=condExp_smul (μ:=J) ((n:ℝ)⁻¹) ((fun z=>∑i,B i z*X i z)-d) V
  have hscore : vectorMeasureOverlapScore (n:=n) μ β t ht.le q=
      (n:ℝ)⁻¹ •((fun z=>∑i,B i z*X i z)-d) := by
    funext z
    simp only [vectorMeasureOverlapScore,normalizedSpinScore,fieldDot,B,X,d,
      Pi.smul_apply,Pi.sub_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [hscore]
  have hm:=ae_all_iff.2 (fun i : Fin n=>vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht q i)
  filter_upwards [hs,hsub,hlin,hm] with z hzs hzsub hzlin hzm
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul] at hzs hzsub
  rw [hzs,hzsub,hdc,hzlin]
  dsimp only [vectorSelfOverlap,d]
  have hsum : (∑i : Fin n,B i z*J[X i|V] z)=‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [hzm i]
    simp only [B,pow_two]
  rw [hsum]
  ring

theorem condVar_vectorMeasureOverlapScore (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    condVar (vectorSpinPast n (q:ℝ).toNNReal) (vectorMeasureOverlapScore (n:=n) μ β t ht.le q)
      (vectorMeasureSpinPathLaw μ β t a ht.le)=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
        (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2 := by
  have hd : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample : VectorDisorderBrownianSample n=>‖vectorMeasureSpinMean μ β t ht.le q sample‖^2/2) := by
    letI : MeasurableSpace (VectorDisorderBrownianSample n):=vectorBrownianFiltration n (q:ℝ).toNNReal
    exact ((adapted_vectorMeasureSpinMean μ β t ht.le q).norm.pow_const 2).div_const 2
  have h:=condVar_vectorMeasure_past_affine_score μ β t a hβ ht q
    (vectorMeasureSpinMean μ β t ht.le q) _
    (adapted_vectorMeasureSpinMean_component μ β t ht.le q) hd 1 ((n:ℝ)/2) zero_le_one
    (fun sample i=>by simpa only [Real.norm_eq_abs] using
      vectorMeasureSpinMean_component_bound μ β t ht.le q sample i)
    (fun sample=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (norm_sq_le_dimension_of_components _
        (fun i=>vectorMeasureSpinMean_component_bound μ β t ht.le q sample i)) (by norm_num))
  exact h

theorem variance_vectorMeasureOverlapScore_total (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le q) (vectorMeasureSpinPathLaw μ β t a ht.le)=
      (∫z : VectorDisorderBrownianSample n×Configuration n,vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
        (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2∂vectorMeasureSpinPathLaw μ β t a ht.le)+
      (1/4)*variance (vectorSelfOverlap (n:=n) μ β t ht.le q) (vectorMeasureSpinPathLaw μ β t a ht.le) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have h:=integral_condVar_add_variance_condExp (vectorSpinPast_le n (q:ℝ).toNNReal)
    (memLp_vectorMeasureOverlapScore (n:=n) μ β t a ht.le q)
  have hc:=integral_congr_ae (condVar_vectorMeasureOverlapScore (n:=n) μ β t a hβ ht q)
  have hv:=variance_congr (condExp_vectorMeasureOverlapScore (n:=n) μ β t a hβ ht q)
  have he : (fun z=>vectorSelfOverlap (n:=n) μ β t ht.le q z/2)=
      (1/2:ℝ) •vectorSelfOverlap μ β t ht.le q := by funext z; simp only [Pi.smul_apply,smul_eq_mul]; ring
  rw [hv,he,variance_smul,hc] at h
  norm_num at h
  exact h.symm

end QuantitativePaper
