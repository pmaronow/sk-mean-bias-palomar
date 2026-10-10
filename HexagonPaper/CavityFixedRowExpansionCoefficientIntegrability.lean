module
public import HexagonPaper.CavityFixedRowExpansionCovarianceBounds
public import HexagonPaper.CavityFixedRowExpansionScalarCoefficients

@[expose] public section

/-! Genuine covariance columns times actual scalar coefficients are
integrable under every finite level law, including free product laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {n : ℕ} {I : Type*} [MeasurableSpace I]

theorem integrable_cavityRestCovarianceColumn_coefficient (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a B : ℝ) (hB : B≠0) (p : Paper.Overlap)
    (ν : Measure I) [IsFiniteMeasure ν] (t pp rr ll : I→Paper.Overlap)
    (ht : Measurable t) (hp : Measurable pp) (hr : Measurable rr) (hl : Measurable ll) (j : Fin 8) :
    Integrable (fun x=>cavityRestCovarianceColumn D μ a p (t x)*scalarResponseCoefficient j B μ (pp x) (rr x) (ll x)) ν := by
  have hSigma : Measurable (fun x=>cavityRestCovarianceColumn D μ a p (t x)) := by
    simpa only [Function.comp_def] using (cavityRestCovarianceColumn D μ a p).continuous.measurable.comp ht
  have hK : Measurable (fun x=>scalarResponseCoefficient j B μ (pp x) (rr x) (ll x)) := by
    simpa only [Function.comp_def] using (continuous_cavityScalarResponseCoefficient_levels j B hB μ).measurable.comp
      (hp.prodMk (hr.prodMk hl))
  have hmeas : AEStronglyMeasurable
      (fun x=>cavityRestCovarianceColumn D μ a p (t x)*scalarResponseCoefficient j B μ (pp x) (rr x) (ll x)) ν := by
    simpa only [Pi.mul_def] using (hSigma.mul hK).aestronglyMeasurable
  apply (integrable_const (1+2*Real.exp (B^2))).mono' hmeas
  exact .of_forall fun x=>by
    rw [norm_mul]
    exact (mul_le_mul (norm_cavityRestCovarianceColumn_apply_le_one D μ a p (t x))
      (norm_cavityScalarResponseCoefficient_le j B hB μ (pp x) (rr x) (ll x))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end HexagonPaper
