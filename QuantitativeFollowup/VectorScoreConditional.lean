module
public import QuantitativePaper.VectorMeasureKernelScoreVariance
public import QuantitativeFollowup.VectorMeanMartingale

@[expose] public section

/-! Actual marked-spin scores conditioned on the whole Wiener/disorder past.
The comparison at earlier levels uses the genuine terminal-spin conditional
law and retains the literal nonnegative mean-increment square. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorSpinPast_mono {p q : Paper.Overlap} (hpq : p≤q) :
    vectorSpinPast n (p:ℝ).toNNReal≤vectorSpinPast n (q:ℝ).toNNReal :=
  MeasurableSpace.comap_mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono hpq))

theorem condExp_vectorMeasureSpinMean_joint_component (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) {q p : Paper.Overlap} (hqp : q≤p) (i : Fin n) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[
      (fun z : VectorDisorderBrownianSample n×Configuration n=>vectorMeasureSpinMean μ β t ht.le p z.1 i)|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>vectorMeasureSpinMean μ β t ht.le q z.1 i := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hp:=vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht p i
  have hq:=vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht q i
  exact (condExp_congr_ae hp.symm).trans
    ((condExp_condExp_of_le (vectorSpinPast_mono hqp) (vectorSpinPast_le n _)).trans hq)

theorem condExp_vectorMeasure_past_affine_score (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n→Field n) (d : VectorDisorderBrownianSample n→ℝ)
    (hb : ∀i,Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] (fun sample=>b sample i))
    (hd : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] d)
    (K D : ℝ) (hK : 0≤K) (hB : ∀sample i,‖b sample i‖≤K) (hD : ∀sample,‖d sample‖≤D) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasurePastAffineSpinScore b d|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>(inner ℝ (b z.1) (vectorMeasureSpinMean μ β t ht.le q z.1)-d z.1)/(n:ℝ) := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=inferInstance
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let m:=vectorSpinPast n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=ambient
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  let B : Fin n→(VectorDisorderBrownianSample n×Configuration n)→ℝ:=fun i z=>b z.1 i
  let X : Fin n→(VectorDisorderBrownianSample n×Configuration n)→ℝ:=fun i z=>Paper.spinSign (z.2 i)
  have hknown (i : Fin n) : StronglyMeasurable[m] (B i):=
    (hb i).stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
  have hX (i : Fin n) : Measurable (X i):=
    (measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i))).comp measurable_snd
  have hs:=condExp_bounded_random_linear (P:=J) m (vectorSpinPast_le n _) B X hknown hX K hK
    (fun i z=>hB z.1 i) (fun i z=>by rw [Real.norm_eq_abs,Paper.abs_spinSign])
  have hlin : Integrable (vectorMeasurePastLinearSpin b) J:=
    bounded_real_integrable _ (measurable_vectorMeasurePastLinearSpin b
      (fun i=>(hb i).mono ((vectorBrownianFiltration n).le _) le_rfl)) _
      (vectorMeasurePastLinearSpin_bound b K hB)
  have hdi : Integrable (fun z : VectorDisorderBrownianSample n×Configuration n=>d z.1) J:=
    bounded_real_integrable _ ((hd.mono ((vectorBrownianFiltration n).le _) le_rfl).comp measurable_fst)
      D (fun z=>hD z.1)
  have hdk : StronglyMeasurable[m] (fun z : VectorDisorderBrownianSample n×Configuration n=>d z.1):=
    hd.stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
  have he : vectorMeasurePastAffineSpinScore b d=
      (n:ℝ)⁻¹ •(vectorMeasurePastLinearSpin b-(fun z=>d z.1)) := by
    funext z
    simp only [vectorMeasurePastAffineSpinScore,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he]
  have hsm:=condExp_smul (μ:=J) (n:ℝ)⁻¹ (vectorMeasurePastLinearSpin b-(fun z=>d z.1)) m
  have hsub:=condExp_sub hlin hdi m
  have hdc:=condExp_of_stronglyMeasurable (vectorSpinPast_le n _) hdk hdi
  change J[(fun z : VectorDisorderBrownianSample n×Configuration n=>d z.1)|m]=
    (fun z=>d z.1) at hdc
  have hspin:=ae_all_iff.2 (fun i : Fin n=>vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht q i)
  filter_upwards [hsm,hsub,hs,hspin] with z hsm hsub hs hspin
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,hdc] at hsm hsub
  change J[vectorMeasurePastLinearSpin b|m] z=∑i,b z.1 i*J[X i|m] z at hs
  have hsum : (∑i : Fin n,b z.1 i*J[X i|m] z)=inner ℝ (b z.1) (vectorMeasureSpinMean μ β t ht.le q z.1) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [hspin i]
    ring
  rw [hsm,hsub,hs,hsum]
  ring

theorem condExp_vectorMeasureOverlapScore_past (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) {p q : Paper.Overlap} (hpq : p≤q) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureOverlapScore μ β t ht.le p|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>(‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2-
        ‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2)/(2*(n:ℝ)) := by
  have hb (i : Fin n) : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>vectorMeasureSpinMean μ β t ht.le p sample i):=
    (adapted_vectorMeasureSpinMean_component μ β t ht.le p i).mono
      ((vectorBrownianFiltration n).mono (Real.toNNReal_mono hpq)) le_rfl
  have hm : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (vectorMeasureSpinMean (n:=n) μ β t ht.le p):=
    (adapted_vectorMeasureSpinMean μ β t ht.le p).mono
      ((vectorBrownianFiltration n).mono (Real.toNNReal_mono hpq)) le_rfl
  have hd : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>‖vectorMeasureSpinMean (n:=n) μ β t ht.le p sample‖^2/2) := by
    letI : MeasurableSpace (VectorDisorderBrownianSample n):=vectorBrownianFiltration n (q:ℝ).toNNReal
    exact (hm.norm.pow_const 2).div_const 2
  have hD (sample : VectorDisorderBrownianSample n) :
      ‖‖vectorMeasureSpinMean μ β t ht.le p sample‖^2/2‖≤(n:ℝ)/2 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (norm_sq_le_dimension_of_components _
      (vectorMeasureSpinMean_component_bound μ β t ht.le p sample)) (by norm_num)
  have h:=condExp_vectorMeasure_past_affine_score μ β t a hβ ht q
    (vectorMeasureSpinMean μ β t ht.le p)
    (fun sample=>‖vectorMeasureSpinMean μ β t ht.le p sample‖^2/2) hb hd
    1 ((n:ℝ)/2) (by norm_num)
    (fun sample i=>by simpa only [Real.norm_eq_abs] using vectorMeasureSpinMean_component_bound μ β t ht.le p sample i)
    hD
  have he : vectorMeasureOverlapScore (n:=n) μ β t ht.le p=
      vectorMeasurePastAffineSpinScore (vectorMeasureSpinMean μ β t ht.le p)
        (fun sample=>‖vectorMeasureSpinMean μ β t ht.le p sample‖^2/2) := by
    funext z
    rfl
  rw [he]
  filter_upwards [h] with z hz
  rw [hz,norm_sub_sq_real,real_inner_comm (vectorMeasureSpinMean μ β t ht.le q z.1)
    (vectorMeasureSpinMean μ β t ht.le p z.1)]
  ring

end QuantitativeFollowup
