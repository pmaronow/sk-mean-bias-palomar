module
public import QuantitativePaper.VectorMeasureRandomReaction
public import FourPapersCommon.WeightedConditionalIntegral

@[expose] public section

/-! Exact covariance decay in a bounded random direction known in the
whole past. Both terminal second moments and mean cross terms are conditioned
under the actual fractional disorder law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem weighted_mean_product_integrable (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (u v : Paper.Overlap) (i j : Fin n)
    (Z : VectorDisorderBrownianSample n → ℝ) (hZ : Measurable Z)
    (K : ℝ≥0) (hK : ∀ sample, ‖Z sample‖≤K) :
    Integrable (fun sample => Z sample*vectorMeasureSpinMean μ β t ht u sample i*
      vectorMeasureSpinMean μ β t ht v sample j) (vectorMeasureDisorderTilt μ β t a) := by
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hMi := (adapted_vectorMeasureSpinMean_component μ β t ht u i).mono
    ((vectorBrownianFiltration n).le _) le_rfl
  have hMj := (adapted_vectorMeasureSpinMean_component μ β t ht v j).mono
    ((vectorBrownianFiltration n).le _) le_rfl
  apply (integrable_const (K:ℝ)).mono' ((hZ.fun_mul hMi).fun_mul hMj).aestronglyMeasurable
  exact .of_forall fun sample => by
    rw [norm_mul,norm_mul]
    have hi : ‖vectorMeasureSpinMean μ β t ht u sample i‖≤1 := by
      simpa only [Real.norm_eq_abs] using vectorMeasureSpinMean_component_bound μ β t ht u sample i
    have hj : ‖vectorMeasureSpinMean μ β t ht v sample j‖≤1 := by
      simpa only [Real.norm_eq_abs] using vectorMeasureSpinMean_component_bound μ β t ht v sample j
    exact (mul_le_mul (mul_le_mul (hK sample) hi (norm_nonneg _) K.coe_nonneg)
      hj (norm_nonneg _) (mul_nonneg K.coe_nonneg zero_le_one)).trans_eq (by ring)

theorem vectorMeasure_weighted_covariance_entry_decay (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q)
    (i j : Fin n) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] Z)
    (K : ℝ≥0) (hK : ∀ sample, ‖Z sample‖≤K) :
    (∫ sample, Z sample*vectorMeasureSpinCovariance μ β t a ht.le r sample i j
      ∂vectorMeasureDisorderTilt μ β t a)-
    (∫ sample, Z sample*vectorMeasureSpinCovariance μ β t a ht.le q sample i j
      ∂vectorMeasureDisorderTilt μ β t a)=
    ∫ sample, Z sample*(vectorMeasureSpinMean μ β t ht.le q sample i-
      vectorMeasureSpinMean μ β t ht.le r sample i)*
      (vectorMeasureSpinMean μ β t ht.le q sample j-
      vectorMeasureSpinMean μ β t ht.le r sample j) ∂vectorMeasureDisorderTilt μ β t a := by
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let V := QuantitativeFollowup.vectorOverlapFiltration n
  let M : Paper.Overlap → VectorDisorderBrownianSample n → Fin n → ℝ :=
    fun u sample l => vectorMeasureSpinMean μ β t ht.le u sample l
  let T := vectorMeasureTerminalObservable μ β t ht.le
    (fun σ => Paper.spinSign (σ i)*Paper.spinSign (σ j))
  have hTi : Integrable T P := integrable_vectorMeasureTerminalObservable μ β t a ht.le _
  have hZm : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hZq := hZ.mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono hrq)) le_rfl
  have hZT : Integrable (fun sample => Z sample*T sample) P :=
    hTi.bdd_mul hZm.aestronglyMeasurable (.of_forall hK)
  have hmean (u v : Paper.Overlap) (l k : Fin n) :
      Integrable (fun sample => Z sample*M u sample l*M v sample k) P :=
    weighted_mean_product_integrable μ β t a ht.le u v l k Z hZm K hK
  have hpast (u : Paper.Overlap)
      (hu : Measurable[vectorBrownianFiltration n (u:ℝ).toNNReal] Z) :
      (∫ sample, Z sample*vectorMeasureSpinCovariance μ β t a ht.le u sample i j ∂P)=
        (∫ sample, Z sample*T sample ∂P)-∫ sample,Z sample*M u sample i*M u sample j ∂P := by
    have hCE := (integrable_condExp (μ:=P) (m:=V u) (f:=T)).bdd_mul
      hZm.aestronglyMeasurable (.of_forall hK)
    have he : (fun sample => Z sample*vectorMeasureSpinCovariance μ β t a ht.le u sample i j)=
        (fun sample => Z sample*P[T|V u] sample)-
          (fun sample => Z sample*M u sample i*M u sample j) := by
      funext sample
      change Z sample*(P[T|V u] sample-M u sample i*M u sample j)=
        Z sample*P[T|V u] sample-Z sample*M u sample i*M u sample j
      ring
    rw [he]
    change (∫ sample,Z sample*P[T|V u] sample-Z sample*M u sample i*M u sample j ∂P)=_
    rw [integral_sub hCE (hmean u u i j),
      integral_known_mul_condExp (V u) (V.le u) Z T hu.stronglyMeasurable hTi hZT]
  have hcross (l k : Fin n) :
      (∫ sample, Z sample*M r sample l*M q sample k ∂P)=
        ∫ sample,Z sample*M r sample l*M r sample k ∂P := by
    have hknown : StronglyMeasurable[V r] (fun sample => Z sample*M r sample l) :=
      (hZ.fun_mul (adapted_vectorMeasureSpinMean_component μ β t ht.le r l)).stronglyMeasurable
    exact integral_known_mul_martingale_cross
      (QuantitativeFollowup.martingale_vectorMeasureSpinMean_component μ β t a hβ ht k)
      hrq _ hknown (hmean r q l k)
  have hcross2 : (∫ sample,Z sample*M q sample i*M r sample j ∂P)=
      ∫ sample,Z sample*M r sample i*M r sample j ∂P := by
    calc
      _ = ∫ sample,Z sample*M r sample j*M q sample i ∂P :=
        integral_congr_ae (.of_forall fun sample => by ring)
      _ = ∫ sample,Z sample*M r sample j*M r sample i ∂P := hcross j i
      _ = _ := integral_congr_ae (.of_forall fun sample => by ring)
  have hexpand : (fun sample => Z sample*(M q sample i-M r sample i)*(M q sample j-M r sample j))=
      ((fun sample => Z sample*M q sample i*M q sample j)-
        (fun sample => Z sample*M q sample i*M r sample j))-
      (fun sample => Z sample*M r sample i*M q sample j)+
        (fun sample => Z sample*M r sample i*M r sample j) := by
    funext sample
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  change _ = ∫ sample,Z sample*(M q sample i-M r sample i)*(M q sample j-M r sample j) ∂P
  rw [hpast r hZ,hpast q hZq,hexpand]
  change _ = ∫ sample,((Z sample*M q sample i*M q sample j-
    Z sample*M q sample i*M r sample j)-Z sample*M r sample i*M q sample j)+
      Z sample*M r sample i*M r sample j ∂P
  have ha := integral_add (((hmean q q i j).sub (hmean q r i j)).sub (hmean r q i j)) (hmean r r i j)
  have hs := integral_sub ((hmean q q i j).sub (hmean q r i j)) (hmean r q i j)
  have hs2 := integral_sub (hmean q q i j) (hmean q r i j)
  simp only [Pi.sub_apply,Pi.add_apply] at ha hs hs2
  rw [ha,hs,hs2,hcross2,hcross i j]
  ring

private theorem weighted_increment_product_integrable (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (r q : Paper.Overlap) (i j : Fin n)
    (Z : VectorDisorderBrownianSample n → ℝ) (hZ : Measurable Z)
    (K : ℝ≥0) (hK : ∀ sample, ‖Z sample‖≤K) :
    Integrable (fun sample => Z sample*(vectorMeasureSpinMean μ β t ht q sample i-
      vectorMeasureSpinMean μ β t ht r sample i)*(vectorMeasureSpinMean μ β t ht q sample j-
      vectorMeasureSpinMean μ β t ht r sample j)) (vectorMeasureDisorderTilt μ β t a) := by
  have hh := (((weighted_mean_product_integrable μ β t a ht q q i j Z hZ K hK).sub
    (weighted_mean_product_integrable μ β t a ht q r i j Z hZ K hK)).sub
    (weighted_mean_product_integrable μ β t a ht r q i j Z hZ K hK)).add
    (weighted_mean_product_integrable μ β t a ht r r i j Z hZ K hK)
  convert hh using 1
  funext sample
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem vectorMeasure_random_covariance_decay (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q)
    (b : VectorDisorderBrownianSample n → Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (K : ℝ≥0) (hK : ∀ sample, ‖b sample‖≤K) :
    (∫ sample,vectorMeasureCovarianceQuadratic μ β t a ht.le q sample (b sample)
      ∂vectorMeasureDisorderTilt μ β t a)=
    (∫ sample,vectorMeasureCovarianceQuadratic μ β t a ht.le r sample (b sample)
      ∂vectorMeasureDisorderTilt μ β t a)-
    ∫ sample,(inner ℝ (b sample) (vectorMeasureSpinMean μ β t ht.le q sample-
      vectorMeasureSpinMean μ β t ht.le r sample))^2 ∂vectorMeasureDisorderTilt μ β t a := by
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let Z : Fin n → Fin n → VectorDisorderBrownianSample n → ℝ :=
    fun i j sample => b sample i*b sample j
  let D : VectorDisorderBrownianSample n → Field n := fun sample =>
    vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample
  have hbi (i : Fin n) : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal]
      (fun sample => b sample i) := (EuclideanSpace.proj i).continuous.measurable.comp hb
  have hZm (i j : Fin n) : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] (Z i j) :=
    (hbi i).fun_mul (hbi j)
  have hZambient (i j : Fin n) : Measurable (Z i j) :=
    (hZm i j).mono ((vectorBrownianFiltration n).le _) le_rfl
  have hZbound (i j : Fin n) (sample : VectorDisorderBrownianSample n) : ‖Z i j sample‖≤((K^2:ℝ≥0):ℝ) := by
    rw [NNReal.coe_pow]
    dsimp only [Z]
    rw [norm_mul]
    exact (mul_le_mul ((PiLp.norm_apply_le (b sample) i).trans (hK sample))
      ((PiLp.norm_apply_le (b sample) j).trans (hK sample)) (norm_nonneg _) K.coe_nonneg).trans_eq (by simp [pow_two])
  have hCint (u : Paper.Overlap) (i j : Fin n) :
      Integrable (fun sample => Z i j sample*vectorMeasureSpinCovariance μ β t a ht.le u sample i j) P := by
    apply (integrable_const (2*(K:ℝ)^2)).mono'
      ((hZambient i j).fun_mul (measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le u i j)).aestronglyMeasurable
    filter_upwards [vectorMeasureSpinCovariance_entry_bound μ β t a ht.le u] with sample hs
    rw [norm_mul,Real.norm_eq_abs]
    have hZb : ‖Z i j sample‖≤(K:ℝ)^2 := by simpa only [NNReal.coe_pow] using hZbound i j sample
    exact (mul_le_mul hZb (hs i j) (abs_nonneg _) (sq_nonneg (K:ℝ))).trans_eq (by ring)
  have hDint (i j : Fin n) : Integrable (fun sample => Z i j sample*D sample i*D sample j) P :=
    weighted_increment_product_integrable μ β t a ht.le r q i j (Z i j) (hZambient i j) (K^2) (hZbound i j)
  have hC (u : Paper.Overlap) :
      (∫ sample,vectorMeasureCovarianceQuadratic μ β t a ht.le u sample (b sample) ∂P)=
      ∑ i : Fin n,∑ j : Fin n,∫ sample,Z i j sample*vectorMeasureSpinCovariance μ β t a ht.le u sample i j ∂P := by
    have he : (fun sample => vectorMeasureCovarianceQuadratic μ β t a ht.le u sample (b sample))=
        fun sample => ∑ i : Fin n,∑ j : Fin n,Z i j sample*vectorMeasureSpinCovariance μ β t a ht.le u sample i j := by
      funext sample
      unfold vectorMeasureCovarianceQuadratic
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [Z]; ring
    rw [he,integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hCint u i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hCint u i j)
  have hD : (∫ sample,(inner ℝ (b sample) (D sample))^2 ∂P)=
      ∑ i : Fin n,∑ j : Fin n,∫ sample,Z i j sample*D sample i*D sample j ∂P := by
    have he : (fun sample => (inner ℝ (b sample) (D sample))^2)=
        fun sample => ∑ i : Fin n,∑ j : Fin n,Z i j sample*D sample i*D sample j := by
      funext sample
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply,conj_trivial]
      rw [pow_two,Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [Z]; ring
    rw [he,integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hDint i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hDint i j)
  have hsum := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun i _ => Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
      (fun j _ => vectorMeasure_weighted_covariance_entry_decay μ β t a hβ ht r q hrq i j
        (Z i j) (hZm i j) (K^2) (hZbound i j)))
  simp only [Finset.sum_sub_distrib] at hsum
  change (∑ i : Fin n,∑ j : Fin n,∫ sample,Z i j sample*vectorMeasureSpinCovariance μ β t a ht.le r sample i j ∂P)-
    (∑ i : Fin n,∑ j : Fin n,∫ sample,Z i j sample*vectorMeasureSpinCovariance μ β t a ht.le q sample i j ∂P)=
      ∑ i : Fin n,∑ j : Fin n,∫ sample,Z i j sample*D sample i*D sample j ∂P at hsum
  rw [←hC r,←hC q,←hD] at hsum
  change _ = _-(∫ sample,(inner ℝ (b sample) (D sample))^2 ∂P)
  linarith

end QuantitativePaper
