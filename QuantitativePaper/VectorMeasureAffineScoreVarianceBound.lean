module
public import QuantitativePaper.VectorMeasureAffineScoreConditionalVariance

@[expose] public section

/-! Genuine total-variance control of a past-dependent terminal-spin score.
The covariance is integrated under the actual fractional disorder law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem measurable_vectorMeasureCovarianceQuadratic_random (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : ∀i,Measurable (fun sample=>b sample i)) :
    Measurable (fun sample=>vectorMeasureCovarianceQuadratic μ β t a ht q sample (b sample)) := by
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  have hM (l : Fin n) : Measurable (vectorMeasureSpinMean μ β t ht q · l) :=
    (adapted_vectorMeasureSpinMean_component μ β t ht q l).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  have hCE : Measurable (fun sample=>(vectorMeasureDisorderTilt μ β t a)[
      vectorMeasureTerminalObservable μ β t ht (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))|
      vectorBrownianFiltration n (q:ℝ).toNNReal] sample) :=
    (stronglyMeasurable_condExp.mono ((vectorBrownianFiltration n).le _)).measurable
  exact ((hCE.sub ((hM i).mul (hM j))).mul (hb i)).mul (hb j)

theorem vectorMeasure_past_affine_score_covariance_le_variance (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n→Field n) (d : VectorDisorderBrownianSample n→ℝ)
    (hb : ∀i,Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] (fun sample=>b sample i))
    (hd : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] d)
    (K D : ℝ) (hK : 0≤K) (hB : ∀sample i,‖b sample i‖≤K) (hD : ∀sample,‖d sample‖≤D) :
    (∫sample,vectorMeasureCovarianceQuadratic μ β t a ht.le q sample (b sample)
      ∂vectorMeasureDisorderTilt μ β t a)/(n:ℝ)^2≤
      variance (vectorMeasurePastAffineSpinScore b d) (vectorMeasureSpinPathLaw μ β t a ht.le) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hbg (i : Fin n) : Measurable (fun sample=>b sample i) :=
    (hb i).mono ((vectorBrownianFiltration n).le _) le_rfl
  have hdg : Measurable d:=hd.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hscore : Measurable (vectorMeasurePastAffineSpinScore b d) :=
    ((measurable_vectorMeasurePastLinearSpin b hbg).sub (hdg.comp measurable_fst)).div_const _
  have hbound (p : VectorDisorderBrownianSample n×Configuration n) :
      ‖vectorMeasurePastAffineSpinScore b d p‖≤((n:ℝ)*K+D)/‖(n:ℝ)‖ := by
    rw [vectorMeasurePastAffineSpinScore,norm_div]
    exact div_le_div_of_nonneg_right
      ((norm_sub_le _ _).trans (add_le_add (vectorMeasurePastLinearSpin_bound b K hB p) (hD p.1)))
      (norm_nonneg _)
  have hL : MemLp (vectorMeasurePastAffineSpinScore b d) 2 J:=
    MemLp.of_bound hscore.aestronglyMeasurable _ (.of_forall hbound)
  have hle:=integral_condVar_le_variance (P:=J) (vectorSpinPast n (q:ℝ).toNNReal)
    (vectorSpinPast_le n _) _ hL
  have he:=integral_congr_ae (condVar_vectorMeasure_past_affine_score μ β t a hβ ht q b d hb hd K D hK hB hD)
  have hcov:=measurable_vectorMeasureCovarianceQuadratic_random μ β t a ht.le q b hbg
  rw [he,integral_div,integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le _ hcov] at hle
  exact hle

end QuantitativePaper
