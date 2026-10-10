module
public import QuantitativePaper.VectorMeasureCovarianceMatrix
public import FourPapersCommon.BoundedLinearConditionalCovariance

@[expose] public section

/-! Conditional covariance of bounded directions known in the whole past,
under the genuine marked terminal-spin law. The predictable offset does
not contribute to the conditional variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def vectorMeasurePastLinearSpin (b : VectorDisorderBrownianSample n→Field n)
    (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  ∑i : Fin n,b p.1 i*Paper.spinSign (p.2 i)

def vectorMeasurePastAffineSpinScore (b : VectorDisorderBrownianSample n→Field n)
    (d : VectorDisorderBrownianSample n→ℝ)
    (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  (vectorMeasurePastLinearSpin b p-d p.1)/(n:ℝ)

theorem condVar_vectorMeasure_past_linear_spin (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : ∀i,Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] (fun sample=>b sample i))
    (K : ℝ) (hK : 0≤K) (hB : ∀sample i,‖b sample i‖≤K) :
    condVar (vectorSpinPast n (q:ℝ).toNNReal) (vectorMeasurePastLinearSpin b)
      (vectorMeasureSpinPathLaw μ β t a ht.le)=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun p=>vectorMeasureCovarianceQuadratic μ β t a ht.le q p.1 (b p.1) := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=inferInstance
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let m:=vectorSpinPast n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=ambient
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  let B : Fin n→(VectorDisorderBrownianSample n×Configuration n)→ℝ := fun i p=>b p.1 i
  let X : Fin n→(VectorDisorderBrownianSample n×Configuration n)→ℝ := fun i p=>Paper.spinSign (p.2 i)
  have hknown (i : Fin n) : StronglyMeasurable[m] (B i) :=
    (hb i).stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
  have hX (i : Fin n) : Measurable (X i) :=
    (measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i))).comp measurable_snd
  have hXB (i : Fin n) (p : VectorDisorderBrownianSample n×Configuration n) : ‖X i p‖≤1 := by
    change ‖Paper.spinSign (p.2 i)‖≤1
    rw [Real.norm_eq_abs,Paper.abs_spinSign]
  have h:=condVar_bounded_random_linear (P:=J) m (vectorSpinPast_le n _) B X
    hknown hX K hK (fun i p=>hB p.1 i) hXB
  have h1:=ae_all_iff.2 (fun i : Fin n=>vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht q i)
  have h2:=ae_all_iff.2 (fun i : Fin n=>ae_all_iff.2 (fun j : Fin n=>
    vectorMeasureSpinPathLaw_terminal_observable_condExp μ β t a ht.le q
      (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))))
  filter_upwards [h,h1,h2] with p hp hmean hsecond
  change condVar m (vectorMeasurePastLinearSpin b) J p=_ at hp
  rw [hp]
  unfold vectorMeasureCovarianceQuadratic
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (b p.1 i*b p.1 j)*
    (J[(fun p : VectorDisorderBrownianSample n×Configuration n=>Paper.spinSign (p.2 i)*Paper.spinSign (p.2 j))|m] p-
      J[(fun p : VectorDisorderBrownianSample n×Configuration n=>Paper.spinSign (p.2 i))|m] p*
      J[(fun p : VectorDisorderBrownianSample n×Configuration n=>Paper.spinSign (p.2 j))|m] p)=_
  rw [hmean i,hmean j,hsecond i j]
  unfold vectorMeasureSpinCovariance
  ring

theorem measurable_vectorMeasurePastLinearSpin (b : VectorDisorderBrownianSample n→Field n)
    (hb : ∀i,Measurable (fun sample=>b sample i)) : Measurable (vectorMeasurePastLinearSpin b) := by
  apply Finset.measurable_sum
  intro i _
  exact (hb i |>.comp measurable_fst).mul
    ((measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i))).comp measurable_snd)

theorem vectorMeasurePastLinearSpin_bound (b : VectorDisorderBrownianSample n→Field n)
    (K : ℝ) (hB : ∀sample i,‖b sample i‖≤K)
    (p : VectorDisorderBrownianSample n×Configuration n) :
    ‖vectorMeasurePastLinearSpin b p‖≤(n:ℝ)*K := by
  calc
    _≤∑i : Fin n,‖b p.1 i*Paper.spinSign (p.2 i)‖ := norm_sum_le _ _
    _≤∑_i : Fin n,K := Finset.sum_le_sum fun i _=>by
      rw [norm_mul,Real.norm_eq_abs (Paper.spinSign _),Paper.abs_spinSign,mul_one]
      exact hB p.1 i
    _=(n:ℝ)*K := by simp

theorem condVar_vectorMeasure_past_affine_score (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n→Field n) (d : VectorDisorderBrownianSample n→ℝ)
    (hb : ∀i,Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] (fun sample=>b sample i))
    (hd : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] d)
    (K D : ℝ) (hK : 0≤K) (hB : ∀sample i,‖b sample i‖≤K) (hD : ∀sample,‖d sample‖≤D) :
    condVar (vectorSpinPast n (q:ℝ).toNNReal) (vectorMeasurePastAffineSpinScore b d)
      (vectorMeasureSpinPathLaw μ β t a ht.le)=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun p=>vectorMeasureCovarianceQuadratic μ β t a ht.le q p.1 (b p.1)/(n:ℝ)^2 := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=inferInstance
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let m:=vectorSpinPast n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=ambient
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hbg (i : Fin n) : Measurable (fun sample=>b sample i) :=
    (hb i).mono ((vectorBrownianFiltration n).le _) le_rfl
  have hdj : StronglyMeasurable[m] (fun p : VectorDisorderBrownianSample n×Configuration n=>d p.1) :=
    hd.stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
  have hdi : Integrable (fun p : VectorDisorderBrownianSample n×Configuration n=>d p.1) J :=
    bounded_real_integrable _ ((hd.mono ((vectorBrownianFiltration n).le _) le_rfl).comp measurable_fst)
      D (fun p=>hD p.1)
  have hXi : Integrable (vectorMeasurePastLinearSpin b) J :=
    bounded_real_integrable _ (measurable_vectorMeasurePastLinearSpin b hbg) _
      (vectorMeasurePastLinearSpin_bound b K hB)
  have he : vectorMeasurePastAffineSpinScore b d=
      (n:ℝ)⁻¹ •(vectorMeasurePastLinearSpin b-(fun p=>d p.1)) := by
    funext p
    simp only [vectorMeasurePastAffineSpinScore,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he]
  have hs:=condVar_smul (m:=m) (μ:=J) (n:ℝ)⁻¹
    (vectorMeasurePastLinearSpin b-(fun p=>d p.1))
  have hz:=condVar_sub_known (P:=J) m (vectorSpinPast_le n _) _ _ hXi hdi hdj
  have hc:=condVar_vectorMeasure_past_linear_spin μ β t a hβ ht q b hb K hK hB
  filter_upwards [hs,hz,hc] with p hp hz hc
  simp only [Pi.smul_apply,smul_eq_mul] at hp
  rw [hp,hz,hc]
  simp only [div_eq_mul_inv,inv_pow,mul_comm]

end QuantitativePaper
