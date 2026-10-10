module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestFuturePairing
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments
public import QuantitativeFollowup.ScalarResponseSamples

@[expose] public section

/-! The scalar K2 future term factors under the true zero-incident-row
marked law. Its rest continuation is conditioned against the actual
centered present self-overlap, producing the genuine covariance column.
Both whole paths and terminal spin marks stay in the source integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem measurable_futureKernel2_rest_test {n : ℕ}
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p r : Paper.Overlap) :
    Measurable (fun sample : AnisotropicDisorderBrownianSample n =>
      cavityRestFutureSquare D μ p r sample *
        cavitySignedResponseCenteredSelfOverlap D μ a p sample) := by
  have hmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n =>
      (p, (r, sample))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hfuture := (measurable_cavityRestFutureSquare D μ).comp hmap
  have hcenter : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
    (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
      ((anisotropicBrownianFiltration n).le _) le_rfl
  exact hfuture.mul hcenter

 theorem cavityZeroMarked_future_scalarSample2_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0:ℝ) 1) (a : ℝ)
    (p r : Paper.Overlap) (hpr : p ≤ r) :
    let D := followupCavityRestSpinModel n β ρ hβ hρ
    let B := followupCavityScalarBeta n β ρ
    (∫z, cavityRestFutureSquare D μ p r (cavityZeroMarkedSampleSplit n z).1.1 *
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1 *
      scalarResponseSample 2 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) =
      cavityRestCovarianceColumn D μ a p r * scalarResponseKernel2 B μ p r 0 := by
  dsimp only
  let D := followupCavityRestSpinModel n β ρ hβ hρ
  let B := followupCavityScalarBeta n β ρ
  let F := fun sample : AnisotropicDisorderBrownianSample n =>
    cavityRestFutureSquare D μ p r sample * cavitySignedResponseCenteredSelfOverlap D μ a p sample
  have hF : Measurable F := measurable_futureKernel2_rest_test D μ a p r
  have hG := measurable_scalarResponseSample 2 B
    (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p r 0
  have he := integral_cavityZeroMarked_product μ n β ρ hβ hρ a
    (fun z => F z.1) (scalarResponseSample 2 B μ p r 0) (hF.comp measurable_fst) hG
  have hmarg : (∫z, F z.1 ∂anisotropicMeasureSpinPathLaw D μ a) =
      ∫sample, F sample ∂anisotropicMeasureSampleLaw D μ a :=
    integral_anisotropicMeasureSpinPathLaw_sample D μ a F hF
  have hrest : (∫z, F z.1 ∂anisotropicMeasureSpinPathLaw D μ a) =
      cavityRestCovarianceColumn D μ a p r := by
    rw [hmarg]
    exact cavityRestFutureSquare_centered_integral_eq_covarianceColumn D μ a p r hpr
  change (∫z, F (cavityZeroMarkedSampleSplit n z).1.1 *
      scalarResponseSample 2 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) = _
  rw [he, hrest, integral_scalarResponseSample]
  rfl

end QuantitativeFollowup
