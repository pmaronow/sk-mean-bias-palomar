module
public import QuantitativeFollowup.StandardSKCovarianceBudget

@[expose] public section

/-! Honest real-valued integrability of both selected response budgets. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem measurable_standardSKSelectedHessianEnergy_joint (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (J : Finset (Fin n)) :
    Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      standardSKSelectedHessianEnergy μ β t ht J z.1 z.2) := by
  have hH : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      vectorMeasureHessianProcess μ β t ht z.1 z.2) :=
    measurable_uncurry_of_continuous_of_measurable (continuous_vectorMeasureHessianProcess_path μ β t ht)
      (fun q=>(adapted_vectorMeasureHessianProcess μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl)
  have hM:=(anisotropicSelectedFieldMap J).continuous.measurable.comp
    (measurable_standardSKSpinMean_joint (n:=n) μ β t ht)
  have hE : Continuous (fun p : (Field n→L[ℝ]Field n)×Field n=>p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hE.measurable.comp (hH.prodMk hM)).inner hM

theorem norm_standardSKSelectedHessianEnergy_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (J : Finset (Fin n)) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    ‖standardSKSelectedHessianEnergy μ β t ht J q sample‖ ≤ (n:ℝ)*(standardSKSelectedBound J)^2 := by
  let m:=standardSKSelectedMean μ β t ht J q sample
  have hb : ‖m‖ ≤ standardSKSelectedBound J:=norm_standardSKSelectedMean_le μ β t ht J q sample
  calc
    _ ≤ ‖vectorMeasureHessianProcess μ β t ht q sample m‖*‖m‖:=norm_inner_le_norm _ _
    _ ≤ ((n:ℝ)*‖m‖)*‖m‖:=mul_le_mul_of_nonneg_right
      (((vectorMeasureHessianProcess μ β t ht q sample).le_opNorm m).trans
        (mul_le_mul_of_nonneg_right (norm_vectorMeasureHessianProcess_le μ β t ht q sample) (norm_nonneg _)))
      (norm_nonneg _)
    _ ≤ (n:ℝ)*(standardSKSelectedBound J)^2:=by
      rw [mul_assoc,←pow_two]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (Nat.cast_nonneg n)

theorem norm_standardSKSelectedCovarianceExpectation_le (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (J : Finset (Fin n)) (q : Paper.Overlap) :
    ‖∫sample,standardSKSelectedCovarianceEnergy μ β t a ht J q sample ∂vectorMeasureDisorderTilt μ β t a‖ ≤ 
      2*(n:ℝ)^2*(standardSKSelectedBound J)^2 := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply (norm_integral_le_integral_norm _).trans
  have hb : ∀ᵐsample ∂vectorMeasureDisorderTilt μ β t a,
      ‖standardSKSelectedCovarianceEnergy μ β t a ht J q sample‖ ≤ 
        2*(n:ℝ)^2*(standardSKSelectedBound J)^2 := by
    filter_upwards [vectorMeasureCovarianceQuadratic_uniform_bound μ β t a ht q] with sample hs
    rw [Real.norm_eq_abs]
    exact (hs _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_standardSKSelectedMean_le μ β t ht J q sample) 2) (by positivity))
  exact (integral_mono_ae (integrable_standardSKSelectedCovarianceEnergy μ β t a ht J q).norm
    (integrable_const _) hb).trans_eq (by simp)

theorem integrable_standardSKWeightedEnergyBudgets (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (J : Finset (Fin n)) (κ : Paper.Overlap→ℝ)
    (hL : MemLp κ 2 (parisiFreeMeasure μ a)) :
    Integrable (fun q=>(κ q)^2*(∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a)) (parisiFreeMeasure μ a) ∧
    Integrable (fun q=>(κ q)^2*(∫sample,standardSKSelectedCovarianceEnergy μ β t a ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a)) (parisiFreeMeasure μ a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  have hHm : Measurable (fun q=>∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a) :=
    (measurable_standardSKSelectedHessianEnergy_joint μ β t ht.le J).stronglyMeasurable.integral_prod_right'.measurable
  have hHb (q : Paper.Overlap) : ‖∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a‖ ≤ (n:ℝ)*(standardSKSelectedBound J)^2 := by
    apply (norm_integral_le_of_norm_le (integrable_const _) (.of_forall
      (norm_standardSKSelectedHessianEnergy_le μ β t ht.le J q))).trans_eq
    simp
  constructor
  · exact hL.integrable_sq.mul_bdd hHm.aestronglyMeasurable (.of_forall hHb)
  · exact hL.integrable_sq.mul_bdd
      (measurable_standardSKSelectedCovarianceExpectation μ β t a hβ ht J).aestronglyMeasurable
      (.of_forall (norm_standardSKSelectedCovarianceExpectation_le μ β t a ht.le J))

end QuantitativeFollowup
