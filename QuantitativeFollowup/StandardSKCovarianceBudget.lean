module
public import QuantitativeFollowup.StandardSKSelectedObservables
public import FourPapersCommon.BoundedLinearConditionalCovariance

@[expose] public section

/-! The selected conditional covariance budget is a genuine expectation.
Its measurability follows from the actual total-variance identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def standardSKSelectedBound (J : Finset (Fin n)) : ℝ := ‖anisotropicSelectedFieldMap J‖*Real.sqrt (n:ℝ)

theorem standardSKSelectedBound_nonneg (J : Finset (Fin n)) : 0 ≤ standardSKSelectedBound J := by
  unfold standardSKSelectedBound;positivity

theorem norm_standardSKSelectedMean_le (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (J : Finset (Fin n)) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    ‖standardSKSelectedMean μ β t ht J q sample‖ ≤ standardSKSelectedBound J :=
  ((anisotropicSelectedFieldMap J).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_vectorMeasureGradient_le μ β t ht q sample.1 _) (norm_nonneg _))

theorem adapted_standardSKSelectedMean_component (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (J : Finset (Fin n)) (q : Paper.Overlap) (i : Fin n) :
    Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>standardSKSelectedMean μ β t ht J q sample i) :=
  (EuclideanSpace.proj i).continuous.measurable.comp
    ((anisotropicSelectedFieldMap J).continuous.measurable.comp (adapted_vectorMeasureSpinMean μ β t ht q))

def standardSKSelectedTerminalScore (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (J : Finset (Fin n)) (q : Paper.Overlap) (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  ∑i : Fin n,standardSKSelectedMean μ β t ht J q p.1 i*Paper.spinSign (p.2 i)

def standardSKSelectedPastScore (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (J : Finset (Fin n)) (q : Paper.Overlap) (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  ∑i : Fin n,standardSKSelectedMean μ β t ht J q p.1 i*vectorMeasureSpinMean μ β t ht q p.1 i

theorem standardSKSelectedScore_condExp (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (J : Finset (Fin n)) (q : Paper.Overlap) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[standardSKSelectedTerminalScore μ β t ht.le J q|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      standardSKSelectedPastScore μ β t ht.le J q := by
  let P:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  let b:=fun i : Fin n=>fun p : VectorDisorderBrownianSample n×Configuration n=>
    standardSKSelectedMean μ β t ht.le J q p.1 i
  let X:=fun i : Fin n=>fun p : VectorDisorderBrownianSample n×Configuration n=>Paper.spinSign (p.2 i)
  have hb (i : Fin n) : StronglyMeasurable[vectorSpinPast n (q:ℝ).toNNReal] (b i) :=
    (adapted_standardSKSelectedMean_component μ β t ht.le J q i).stronglyMeasurable.comp_measurable
      (comap_measurable Prod.fst)
  have hx (i : Fin n) : Measurable (X i) :=
    (measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i))).comp measurable_snd
  have hbb (i : Fin n) (p : VectorDisorderBrownianSample n×Configuration n) :
      ‖b i p‖ ≤ standardSKSelectedBound J :=
    (PiLp.norm_apply_le _ i).trans (norm_standardSKSelectedMean_le μ β t ht.le J q p.1)
  have hxb (i : Fin n) (p : VectorDisorderBrownianSample n×Configuration n) : ‖X i p‖ ≤ 1 := by
    simp [X,Real.norm_eq_abs]
  have hh:=condExp_bounded_random_linear (P:=P) (vectorSpinPast n (q:ℝ).toNNReal)
    (vectorSpinPast_le n _) b X hb hx (standardSKSelectedBound J) (standardSKSelectedBound_nonneg J) hbb hxb
  filter_upwards [hh,ae_all_iff.2 (fun i : Fin n=>vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht q i)]
    with p hp hs
  change P[standardSKSelectedTerminalScore μ β t ht.le J q|_ ] p=_ at hp
  rw [hp]
  unfold standardSKSelectedPastScore
  apply Finset.sum_congr rfl
  intro i _
  change b i p*P[X i|_] p=_
  rw [hs i]

private theorem measurable_variance_family {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (F : E×Ω→ℝ) (hF : Measurable F) :
    Measurable (fun x=>variance (fun ω=>F (x,ω)) P) := by
  have hM : Measurable (fun x=>∫ω,F (x,ω) ∂P):=hF.stronglyMeasurable.integral_prod_right'.measurable
  have hR : Measurable (fun z : E×Ω=>(F z-(∫ω,F (z.1,ω) ∂P))^2) :=
    (hF.sub (hM.comp measurable_fst)).pow_const 2
  have he (x : E) : variance (fun ω=>F (x,ω)) P=∫ω,(F (x,ω)-(∫ω,F (x,ω) ∂P))^2 ∂P :=
    variance_eq_integral (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
  simp_rw [he]
  exact hR.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_standardSKSelectedScore_joint (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (J : Finset (Fin n)) :
    Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      standardSKSelectedTerminalScore μ β t ht J z.1 z.2) ∧
    Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      standardSKSelectedPastScore μ β t ht J z.1 z.2) := by
  have hmap : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hM := (measurable_standardSKSpinMean_joint (n:=n) μ β t ht).comp hmap
  have hB:= (anisotropicSelectedFieldMap J).continuous.measurable.comp hM
  constructor
  · apply Finset.measurable_sum
    intro i _
    exact ((EuclideanSpace.proj i).continuous.measurable.comp hB).mul
      ((measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i))).comp measurable_snd.snd)
  · apply Finset.measurable_sum
    intro i _
    exact ((EuclideanSpace.proj i).continuous.measurable.comp hB).mul
      ((EuclideanSpace.proj i).continuous.measurable.comp hM)

theorem norm_standardSKSelectedScores_le (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (J : Finset (Fin n)) (q : Paper.Overlap) (p : VectorDisorderBrownianSample n×Configuration n) :
    ‖standardSKSelectedTerminalScore μ β t ht J q p‖ ≤ (n:ℝ)*standardSKSelectedBound J ∧
    ‖standardSKSelectedPastScore μ β t ht J q p‖ ≤ (n:ℝ)*standardSKSelectedBound J := by
  have hb (i : Fin n) : ‖standardSKSelectedMean μ β t ht J q p.1 i‖ ≤ standardSKSelectedBound J :=
    (PiLp.norm_apply_le _ i).trans (norm_standardSKSelectedMean_le μ β t ht J q p.1)
  have hg (i : Fin n) : ‖vectorMeasureSpinMean μ β t ht q p.1 i‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using vectorMeasureSpinMean_component_bound μ β t ht q p.1 i
  have hs (i : Fin n) : ‖Paper.spinSign (p.2 i)‖ ≤ 1:=by simp [Real.norm_eq_abs]
  have he (X : Fin n→ℝ) (hX : ∀i,‖X i‖ ≤ 1) :
      ‖∑i : Fin n,standardSKSelectedMean μ β t ht J q p.1 i*X i‖ ≤ (n:ℝ)*standardSKSelectedBound J := by
    calc
      _ ≤ ∑i : Fin n,‖standardSKSelectedMean μ β t ht J q p.1 i*X i‖:=norm_sum_le _ _
      _ ≤ ∑_i : Fin n,standardSKSelectedBound J := Finset.sum_le_sum fun i _=>by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul (hb i) (hX i) (norm_nonneg _) (standardSKSelectedBound_nonneg J)
      _=_:=by simp
  exact ⟨he _ hs,he _ hg⟩

theorem integral_standardSKSelectedCovarianceEnergy_eq_variances (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (J : Finset (Fin n)) (q : Paper.Overlap) :
    (∫sample,standardSKSelectedCovarianceEnergy μ β t a ht.le J q sample ∂vectorMeasureDisorderTilt μ β t a)=
      variance (standardSKSelectedTerminalScore μ β t ht.le J q) (vectorMeasureSpinPathLaw μ β t a ht.le)-
      variance (standardSKSelectedPastScore μ β t ht.le J q) (vectorMeasureSpinPathLaw μ β t a ht.le) := by
  let P:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hS : MemLp (standardSKSelectedTerminalScore μ β t ht.le J q) 2 P :=
    MemLp.of_bound (((measurable_standardSKSelectedScore_joint μ β t ht.le J).1).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
      (.of_forall fun p=>(norm_standardSKSelectedScores_le μ β t ht.le J q p).1)
  have hv:=condVar_vectorMeasure_past_linear_spin μ β t a hβ ht q _
    (adapted_standardSKSelectedMean_component μ β t ht.le J q)
    (standardSKSelectedBound J) (standardSKSelectedBound_nonneg J)
    (fun sample i=>(PiLp.norm_apply_le _ i).trans (norm_standardSKSelectedMean_le μ β t ht.le J q sample))
  have he:=integral_condVar_add_variance_condExp (vectorSpinPast_le n (q:ℝ).toNNReal) hS
  have hce:=standardSKSelectedScore_condExp μ β t a hβ ht J q
  rw [variance_congr hce] at he
  have hint:=integral_congr_ae hv
  rw [integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le _
    (measurable_vectorMeasureCovarianceQuadratic_random μ β t a ht.le q _
      (fun i=>(EuclideanSpace.proj i).continuous.measurable.comp (measurable_standardSKSelectedMean μ β t ht.le J q)))] at hint
  change (∫_,condVar _ (standardSKSelectedTerminalScore μ β t ht.le J q) P _ ∂P)=_ at hint
  rw [hint] at he
  exact eq_sub_of_add_eq he

theorem measurable_standardSKSelectedCovarianceExpectation (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (J : Finset (Fin n)) :
    Measurable (fun q=>∫sample,standardSKSelectedCovarianceEnergy μ β t a ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a) := by
  let P:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hT : Measurable (fun q=>variance (standardSKSelectedTerminalScore μ β t ht.le J q) P) :=
    measurable_variance_family P
      (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>standardSKSelectedTerminalScore μ β t ht.le J z.1 z.2)
      (measurable_standardSKSelectedScore_joint μ β t ht.le J).1
  have hS : Measurable (fun q=>variance (standardSKSelectedPastScore μ β t ht.le J q) P) :=
    measurable_variance_family P
      (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>standardSKSelectedPastScore μ β t ht.le J z.1 z.2)
      (measurable_standardSKSelectedScore_joint μ β t ht.le J).2
  convert hT.sub hS using 1
  funext q
  exact integral_standardSKSelectedCovarianceEnergy_eq_variances μ β t a hβ ht J q

end QuantitativeFollowup
